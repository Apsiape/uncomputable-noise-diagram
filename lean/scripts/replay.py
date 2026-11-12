"""Serial Lean source replay of the release package, with memory floor, process-tree cap and receipts.
(Adapted from the hard-model relay, /opt/undecidable-phase-diagram-arxiv-2026-11-11/project/scripts/replay.py,
itself adapted from the forgetting relay's.)

Compiled from source here, one Lean process at a time (`lean -j1 -M5000`, LEAN_NUM_THREADS=1, 1800 s
timeout per module), into this package's `.lake/build/lib/lean`:
  * this package: `UncomputableNoiseDiagram.*` and the package modules `Challenge`, `Solution`, `Audit`;
  * the two vendored cores, exactly the modules this package imports (transitively):
    `FixedNoiseErgodicity.*` from `vendor/FixedNoiseErgodicity`, `UndecidablePhaseDiagram.*` from
    `vendor/UndecidablePhaseDiagram` (byte-identical copies of the released cores).
Mathlib and its dependencies are read from the prebuilt objects of the nine pinned path packages under
`vendor/` and are never rebuilt (a missing object is an error).

Guards (before every Lean process): an exclusive lock, no other `lean` process running, and at least
8 GiB available, the minimum of Linux MemAvailable and the Windows host heartbeat
`.host-memory.json` (written by `host-memory-monitor.py`, refused if older than 20 s). A
process-tree RSS watchdog (`scripts/resource_guard.py`) stops everything at 9.0 GB.

Usage (inside WSL, from the package directory): python3 -I -B scripts/replay.py [--resume] [MODULE ...]
"""
from pathlib import Path
import os, sys, re, json, hashlib, argparse, subprocess, time, signal, shutil, fcntl, importlib.util

P = Path(__file__).resolve().parents[1]
ap = argparse.ArgumentParser()
ap.add_argument('--resume', action='store_true')
ap.add_argument('--lean-bin', type=Path)
ap.add_argument('modules', nargs='*')
A = ap.parse_args()
W = P / '.lake/replay'
W.mkdir(parents=True, exist_ok=True)
OUT = P / '.lake/build/lib/lean'
T = A.lean_bin or Path(os.environ.get('UND_LEAN_BIN', str(P.parent / 'toolchain/bin')))
if not (T / 'lean').is_file():
    T = Path(shutil.which('lean')).parent
lean = T / 'lean'
DEPS = ['plausible', 'LeanSearchClient', 'importGraph', 'proofwidgets', 'aesop', 'Qq', 'batteries', 'Cli', 'mathlib']
deps = [P / 'vendor' / d for d in DEPS]
CORES = {'FixedNoiseErgodicity': P / 'vendor/FixedNoiseErgodicity',
         'UndecidablePhaseDiagram': P / 'vendor/UndecidablePhaseDiagram'}
env = os.environ.copy()
env.update({'PATH': str(T) + os.pathsep + env.get('PATH', ''),
            'LEAN_PATH': os.pathsep.join([str(OUT)] + [str(d / '.lake/build/lib/lean') for d in deps]),
            'LEAN_SRC_PATH': os.pathsep.join(map(str, [P, *CORES.values(), *deps])),
            'LEAN_NUM_THREADS': '1', 'PYTHONDONTWRITEBYTECODE': '1'})
for k in ['TMPDIR', 'TMP', 'TEMP', 'LAKE_CACHE_DIR', 'MATHLIB_CACHE_DIR']:
    d = W / k
    d.mkdir(exist_ok=True)
    env[k] = str(d)
spec = importlib.util.spec_from_file_location('resource_guard', P / 'scripts/resource_guard.py')
guard = importlib.util.module_from_spec(spec)
spec.loader.exec_module(guard)
guard.CAP = 9_900_000_000          # the watchdog stops at min(CAP - 0.1 GB, 9.0 GB) = 9.0 GB
get_peak = guard.memory_cap()
LEAN_MB = 5000
# Per-module Lean options. `UndecidablePhaseDiagram/Statements.lean` (frozen, sha256 ef3ebe7f...) is
# compiled exactly as in the hard-model release (its scripts/replay.py, MODULE_OPTIONS): Mathlib's
# `deriving Fintype` for its enumeration types needs this Lean 4.35 compatibility option.
MODULE_OPTIONS = {'UndecidablePhaseDiagram.Statements': ['-Dbackward.isDefEq.respectTransparency=false']}
IMPORT_RE = re.compile(r'^\s*(?:(?:public|private)\s+)?import\s+([\w.]+)', re.M)


def sha(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def free_bytes():
    info = dict((k, int(v.split()[0]) * 1024) for k, v in
                (x.split(':', 1) for x in Path('/proc/meminfo').read_text().splitlines()))
    host = json.loads((P / '.host-memory.json').read_text())
    if time.time() - host['utc_epoch'] > 20:
        raise SystemExit('REFUSE: the Windows host-memory heartbeat is stale')
    return min(info['MemAvailable'], host['available_bytes'])


def other_lean():
    r = subprocess.run(['pgrep', '-x', 'lean'], capture_output=True, text=True)
    return [x for x in r.stdout.split() if x.strip()]


def locate(n):
    """(kind, root, source, object) of module n: kind 'pkg' (this package), 'core' (a vendored core),
    'dep' (a prebuilt pinned dependency); None for the toolchain's own modules."""
    rel = Path(n.replace('.', '/') + '.lean')
    top = n.split('.')[0]
    obj = OUT / rel.with_suffix('.olean')
    if top in CORES:
        src = CORES[top] / rel
        return ('core', CORES[top], src, obj) if src.is_file() else None
    if (P / rel).is_file():
        return ('pkg', P, P / rel, obj)
    for d in deps:
        if (d / rel).is_file():
            o = d / '.lake/build/lib/lean' / rel.with_suffix('.olean')
            if not o.is_file():
                raise SystemExit(f'missing prebuilt dependency object {o}')
            return ('dep', d, d / rel, o)
    return None


lock = open(W / 'replay.lock', 'w')
try:
    fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
except BlockingIOError:
    raise SystemExit('REFUSE: another replay holds the lock')
if free_bytes() < 8 * 1024 ** 3:
    raise SystemExit('REFUSE: below 8 GiB available physical memory')
version = subprocess.check_output([str(lean), '--version'], env=env, text=True).strip()
assert '4.35.0' in version and 'eb6cafb7290e' in version, version
mods = A.modules or json.loads((P / 'scripts/modules.json').read_text()) + ['Challenge', 'Solution', 'Audit']
seen, ordered = set(), []


def visit(n):
    if n in seen:
        return
    seen.add(n)
    loc = locate(n)
    if loc is None or loc[0] == 'dep':
        return
    for d in IMPORT_RE.findall(loc[2].read_text(encoding='utf-8')):
        visit(d)
    ordered.append((n, *loc))


for n in mods:
    if locate(n) is None:
        raise SystemExit(f'unknown module {n}')
    visit(n)
cachepath = W / 'completed.json'
cache = json.loads(cachepath.read_text()) if A.resume and cachepath.exists() else {}
records = []
for n, kind, root, src, obj in ordered:
    imports = {}
    for d in IMPORT_RE.findall(src.read_text(encoding='utf-8')):
        loc = locate(d)
        if loc and loc[3].exists():
            imports[d] = sha(loc[3])
    sig = {'source': sha(src), 'imports': imports}
    if n in MODULE_OPTIONS:
        sig['options'] = MODULE_OPTIONS[n]
    if A.resume and obj.exists() and cache.get(n) == sig:
        continue
    available = free_bytes()
    if available < 8 * 1024 ** 3:
        raise SystemExit(f'REFUSE {n}: only {available} bytes available (< 8 GiB)')
    running = other_lean()
    if running:
        raise SystemExit(f'REFUSE {n}: lean process(es) already running: {running}')
    obj.parent.mkdir(parents=True, exist_ok=True)
    log = W / (n + '.log')
    cmd = [str(lean), '-j1', f'-M{LEAN_MB}', *MODULE_OPTIONS.get(n, []), '-o', str(obj),
           '-i', str(obj.with_suffix('.ilean')), str(src.relative_to(root))]
    start = time.monotonic()
    print('BUILD', n, kind, 'free_GiB', round(available / 1024 ** 3, 2), flush=True)
    with log.open('wb') as f:
        proc = subprocess.Popen(cmd, cwd=root, env=env, stdout=f, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            rc = proc.wait(timeout=1800)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
            rc = 124
    text = log.read_text(encoding='utf-8', errors='replace')
    record = {'module': n, 'kind': kind, 'exit': rc, 'seconds': round(time.monotonic() - start, 3),
              'peak_tree_bytes': get_peak(), 'free_before_bytes': available, 'command': cmd, 'cwd': str(root),
              'warnings': text.count(': warning:'), 'log_sha256': sha(log)}
    records.append(record)
    print('RESULT', n, rc, record['seconds'], 's; warnings', record['warnings'], '; peak',
          round(get_peak() / 1024 ** 3, 3), 'GiB', flush=True)
    (W / 'latest.json').write_text(json.dumps({'lean': version, 'records': records, 'limit_bytes': 9_000_000_000}, indent=2) + '\n')
    with (W / 'history.ndjson').open('a') as f:
        f.write(json.dumps(record) + '\n')
    if rc:
        print(text[-25000:], flush=True)
        sys.exit(rc)
    cache[n] = sig
    cachepath.write_text(json.dumps(cache, indent=2) + '\n')
    if n == 'Audit':
        shutil.copy2(log, P / 'AXIOMS.txt')
print('REPLAY PASS', len(ordered), 'reachable modules compiled here; peak', get_peak(), flush=True)
