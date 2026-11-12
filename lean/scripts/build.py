"""Serial, memory-capped Lean build for the uncomputable-noise-diagram core (runs inside WSL).

Usage (inside the distro, from /opt/uncomputable-noise-diagram-lean/project):
  python3 -I -B scripts/build.py                 # build every module reachable from the roots
  python3 -I -B scripts/build.py MOD [MOD ...]   # build these modules (and their own deps)
  python3 -I -B scripts/build.py --check FILE    # elaborate one scratch file, no output files

Safety rules (owner's brief, session 1):
  * one Lean process at a time: an exclusive lock file, and a refusal if any `lean` process runs;
  * before every Lean process: at least 8 GiB MemAvailable in the distro, else refuse;
  * every Lean process: `-j1 -M5000`, LEAN_NUM_THREADS=1, a 1800 s timeout; on timeout only the
    process group started here is killed.
Reused libraries are read from prebuilt .olean trees (scripts/env.sh); nothing outside
/opt/uncomputable-noise-diagram-lean is written.
"""
from pathlib import Path
import argparse, fcntl, hashlib, json, os, re, signal, subprocess, sys, time

P = Path(__file__).resolve().parents[1]
ROOT = Path('/opt/uncomputable-noise-diagram-lean')
FNE = Path('/opt/forgetting-arxiv-2026-11-10/project')
UPD = Path('/opt/undecidable-phase-diagram-arxiv-2026-11-11/project')
OUT = P / '.lake/build/lib/lean'
LOGS = P / '.lake/logs'
ROOTS = ['UncomputableNoiseDiagram', 'UncomputableNoiseDiagram.Audit']
MIN_AVAIL = 8 * 1024 ** 3
MEM_MB = 5000
TIMEOUT = 1800
IMPORT_RE = re.compile(r'^\s*(?:(?:public|private)\s+)?import\s+([\w.]+)', re.M)


def env():
    e = os.environ.copy()
    lp = [OUT, FNE / '.lake/build/lib/lean', UPD / '.lake/build/lib/lean']
    sp = [P, FNE, UPD]
    for d in sorted((ROOT / 'vendor').iterdir()):
        if d.is_dir():
            lp.append(d / '.lake/build/lib/lean')
            sp.append(d)
    e['LEAN_PATH'] = ':'.join(map(str, lp))
    e['LEAN_SRC_PATH'] = ':'.join(map(str, sp))
    e['LEAN_NUM_THREADS'] = '1'
    e['PATH'] = str(ROOT / 'toolchain/bin') + ':' + e.get('PATH', '')
    return e


def avail_bytes():
    for line in Path('/proc/meminfo').read_text().splitlines():
        if line.startswith('MemAvailable:'):
            return int(line.split()[1]) * 1024
    raise RuntimeError('no MemAvailable')


def other_lean_running():
    r = subprocess.run(['pgrep', '-x', 'lean'], capture_output=True, text=True)
    return [x for x in r.stdout.split() if x.strip()]


def guard(label):
    a = avail_bytes()
    if a < MIN_AVAIL:
        raise SystemExit(f'REFUSE {label}: only {a / 1024**3:.2f} GiB available (< 8 GiB)')
    running = other_lean_running()
    if running:
        raise SystemExit(f'REFUSE {label}: lean process(es) already running: {running}')
    return a


def sha(p):
    return hashlib.sha256(p.read_bytes()).hexdigest()


def src_of(mod):
    p = P / (mod.replace('.', '/') + '.lean')
    return p if p.is_file() else None


def own_imports(src):
    return [m for m in IMPORT_RE.findall(src.read_text(encoding='utf-8')) if src_of(m)]


def order(mods):
    seen, out = set(), []
    def visit(m):
        if m in seen:
            return
        seen.add(m)
        s = src_of(m)
        if s is None:
            raise SystemExit(f'unknown module {m}')
        for d in own_imports(s):
            visit(d)
        out.append(m)
    for m in mods:
        visit(m)
    return out


def run_lean(args, log, label):
    a = guard(label)
    print(f'LEAN {label} (avail {a / 1024**3:.1f} GiB)', flush=True)
    t0 = time.monotonic()
    with open(log, 'wb') as f:
        proc = subprocess.Popen(['lean', '-j1', f'-M{MEM_MB}'] + args, cwd=P, env=env(),
                                stdout=f, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            rc = proc.wait(timeout=TIMEOUT)
        except subprocess.TimeoutExpired:
            os.killpg(proc.pid, signal.SIGKILL)
            proc.wait()
            rc = 124
    dt = time.monotonic() - t0
    text = Path(log).read_text(encoding='utf-8', errors='replace')
    nwarn = text.count(': warning:')
    print(f'  exit {rc}, {dt:.1f} s, {nwarn} warnings', flush=True)
    return rc, text


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('--check', type=Path)
    ap.add_argument('--force', action='store_true')
    ap.add_argument('modules', nargs='*')
    A = ap.parse_args()
    LOGS.mkdir(parents=True, exist_ok=True)
    lock = open(ROOT / '.build.lock', 'w')
    try:
        fcntl.flock(lock, fcntl.LOCK_EX | fcntl.LOCK_NB)
    except BlockingIOError:
        raise SystemExit('REFUSE: another build holds the lock')
    if A.check:
        rc, text = run_lean([str(A.check)], LOGS / 'check.log', f'check {A.check}')
        print(text[-30000:])
        sys.exit(rc)
    cache_p = P / '.lake/build/signatures.json'
    cache = json.loads(cache_p.read_text()) if cache_p.exists() else {}
    for m in order(A.modules or ROOTS):
        s = src_of(m)
        obj = OUT / (m.replace('.', '/') + '.olean')
        sig = {'source': sha(s),
               'imports': {d: sha(OUT / (d.replace('.', '/') + '.olean')) for d in own_imports(s)}}
        forced = A.force and m in A.modules
        if not forced and obj.exists() and cache.get(m) == sig:
            continue
        obj.parent.mkdir(parents=True, exist_ok=True)
        rc, text = run_lean(['-o', str(obj), '-i', str(obj.with_suffix('.ilean')),
                             str(s.relative_to(P))], LOGS / f'{m}.log', m)
        if rc != 0:
            print(text[-30000:], flush=True)
            sys.exit(rc)
        cache[m] = sig
        cache_p.write_text(json.dumps(cache, indent=1) + '\n')
    print('BUILD OK', flush=True)


if __name__ == '__main__':
    main()
