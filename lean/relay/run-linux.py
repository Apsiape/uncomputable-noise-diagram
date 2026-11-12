"""Guarded Linux runs for the uncomputable-noise-diagram release package (adapted from
/opt/undecidable-phase-diagram-arxiv-2026-11-11/run-linux.py, itself adapted from the forgetting relay's).

Modes:
  comparator  - the actual `lake comparator --config comparator.json` (bubblewrap sandbox via bwrap-record)
  export      - leanexport of Solution for the three comparator targets
  leanchecker - kernel replay of the export with the toolchain's leanchecker (--from-export)
  nanoda      - kernel replay of the export with the toolchain's nanoda_bin (hard error on other axioms)
  nanoda-negative - negative control: nanoda on the same export with Classical.choice not permitted (must fail)
Every mode refuses to start below 8 GiB available (fresh Windows heartbeat and Linux MemAvailable) or while
another lean/lake/leanexport/leanchecker/nanoda process runs, and runs under a process-tree RSS watchdog
(linux_guard.py; stop at 9.0 GB), one process at a time. These tools take no memory-cap option; every Lean
compiler process started through the package targets runs with -M5000 (scripts/replay.py).
"""
from pathlib import Path
import os, sys, time, json, hashlib, subprocess, resource, importlib.util

W = Path(__file__).resolve().parent
P = W / 'project'
R = W / 'results'
R.mkdir(exist_ok=True)
K = W / 'kernels'
K.mkdir(exist_ok=True)
sys.path.insert(0, str(W))
from linux_guard import guarded_run

DEPS = ['plausible', 'LeanSearchClient', 'importGraph', 'proofwidgets', 'aesop', 'Qq', 'batteries', 'Cli', 'mathlib']


def sha(p):
    h = hashlib.sha256()
    with p.open('rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


host = json.loads((P / '.host-memory.json').read_text())
assert time.time() - host['utc_epoch'] < 20 and host['available_bytes'] >= 8 * 1024 ** 3, 'Host memory floor'
linux = dict((k, int(v.split()[0]) * 1024) for k, v in (x.split(':', 1) for x in Path('/proc/meminfo').read_text().splitlines()))
assert linux['MemAvailable'] >= 8 * 1024 ** 3, 'Linux memory floor'
for name in ['lean', 'lake', 'leanexport', 'leanchecker', 'nanoda_bin']:
    r = subprocess.run(['pgrep', '-x', name], capture_output=True, text=True)
    assert not r.stdout.strip(), f'REFUSE: {name} already running: {r.stdout.split()}'
env = os.environ.copy()
env.update({'PATH': str(W / 'toolchain/bin') + ':' + env.get('PATH', ''), 'LEAN_NUM_THREADS': '1',
            'PYTHONDONTWRITEBYTECODE': '1', 'COMPARATOR_BWRAP': str(W / 'bwrap-record')})
for k in ['TMPDIR', 'TMP', 'TEMP', 'LAKE_CACHE_DIR', 'MATHLIB_CACHE_DIR']:
    d = W / 'environment' / k
    d.mkdir(parents=True, exist_ok=True)
    env[k] = str(d)
resource.setrlimit(resource.RLIMIT_CORE, (0, 0))
mode = sys.argv[1]
common = {'host_free_before_bytes': host['available_bytes'], 'linux_available_before_bytes': linux['MemAvailable'], 'threads': 1}
if mode == 'comparator':
    cmd = [str(W / 'toolchain/bin/lake'), 'comparator', '--config', 'comparator.json']
    with (R / 'comparator.log').open('wb') as f:
        rec = guarded_run(cmd, cwd=P, env=env, stdout=f, stderr=-2, start_new_session=True)
    rec.update({'command': cmd, 'sandbox_requested': True, 'supplied_exports': False, **common,
                'lean_version': subprocess.check_output([str(W / 'toolchain/bin/lean'), '--version'], text=True).strip(),
                'bwrap_version': subprocess.check_output([str(W / 'bubblewrap/usr/bin/bwrap'), '--version'], text=True).strip(),
                'lake_sha256': sha(W / 'toolchain/bin/lake'), 'bwrap_sha256': sha(W / 'bubblewrap/usr/bin/bwrap'),
                'log_sha256': sha(R / 'comparator.log')})
    (R / 'comparator-receipt.json').write_text(json.dumps(rec, indent=2) + '\n')
    print(json.dumps(rec), flush=True)
    print((R / 'comparator.log').read_text(errors='replace')[-12000:], flush=True)
    sys.exit(rec['exit'])
elif mode == 'export':
    spec = importlib.util.spec_from_file_location('guard', P / 'scripts/resource_guard.py')
    g = importlib.util.module_from_spec(spec)
    spec.loader.exec_module(g)
    cfg = json.loads((P / 'comparator.json').read_text())
    roots = list(cfg['theorem_names'])
    env['LEAN_PATH'] = ':'.join([str(P / '.lake/build/lib/lean')] + [str(P / 'vendor' / d / '.lake/build/lib/lean') for d in DEPS])
    cmd = [str(W / 'toolchain/bin/leanexport'), 'Solution', '--', *g.export_targets(cfg)]
    with (R / 'Solution.ndjson').open('wb') as f, (R / 'export.log').open('wb') as e:
        rec = guarded_run(cmd, cwd=P, env=env, stdout=f, stderr=e, start_new_session=True)
    rec.update({'command': cmd, 'lean_path': env['LEAN_PATH'], 'roots': roots, **common,
                'sha256': sha(R / 'Solution.ndjson'), 'bytes': (R / 'Solution.ndjson').stat().st_size,
                'binary_sha256': sha(W / 'toolchain/bin/leanexport')})
    (R / 'export-receipt.json').write_text(json.dumps(rec, indent=2) + '\n')
    print(json.dumps(rec), flush=True)
    sys.exit(rec['exit'])
elif mode in ('leanchecker', 'nanoda', 'nanoda-negative'):
    export = R / 'Solution.ndjson'
    xr = json.loads((R / 'export-receipt.json').read_text())
    assert sha(export) == xr['sha256'], 'export digest changed'
    if mode == 'leanchecker':
        binary = W / 'toolchain/bin/leanchecker'
        cmd = [str(binary), '--from-export', str(export)]
        extra = {}
    else:
        binary = W / 'toolchain/bin/nanoda_bin'
        neg = mode == 'nanoda-negative'
        cfgp = K / ('nanoda-negative-control.json' if neg else 'nanoda.json')
        permitted = ['propext', 'Quot.sound'] if neg else ['propext', 'Classical.choice', 'Quot.sound']
        ncfg = {'use_stdin': False, 'export_file_path': str(export), 'num_threads': 1, 'nat_extension': True,
                'string_extension': True, 'permitted_axioms': permitted, 'unpermitted_axiom_hard_error': True}
        cfgp.write_text(json.dumps(ncfg, indent=2) + '\n')
        cmd = [str(binary), str(cfgp)]
        # num_threads 1: nanoda checks serially on the main thread; 128 MiB main-thread stack, as in both
        # precedent relays (RLIMIT_STACK applies to the main thread).
        stack = 134217728
        resource.setrlimit(resource.RLIMIT_STACK, (stack, stack))
        extra = {'stack_rlimit_bytes': stack, 'config': ncfg}
        if neg:
            extra.update({'purpose': 'negative control: same export, Classical.choice removed from permitted_axioms; nanoda must reject',
                          'expected': 'nonzero exit'})
    name = 'nanoda-negative-control' if mode == 'nanoda-negative' else mode
    log = K / (name + '.log')
    with log.open('wb') as f:
        rec = guarded_run(cmd, cwd=W, env=env, stdout=f, stderr=-2, start_new_session=True)
    rec.update({'command': cmd, 'binary_path': str(binary), 'binary_sha256': sha(binary), 'export_sha256': xr['sha256'],
                'export_bytes': xr['bytes'], **common, **extra, 'log_sha256': sha(log),
                'log_tail': log.read_text(errors='replace')[-2000:]})
    (K / (name + '-receipt.json')).write_text(json.dumps(rec, indent=2) + '\n')
    print(json.dumps(rec), flush=True)
    sys.exit(rec['exit'] if mode != 'nanoda-negative' else (0 if rec['exit'] != 0 else 1))
else:
    raise ValueError(mode)
