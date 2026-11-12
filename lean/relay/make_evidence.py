"""Collect the release evidence (run in WSL with python3 -I -B after build, comparator, export, kernels).
(Adapted from the hard-model relay's make_evidence.py.) Writes evidence/{BUILD,COMPARATOR,KERNEL-REPLAY,
AXIOM-AUDIT,SOURCE-AUDIT,CHOICES,ORIGINAL-SOURCE,BINARY-DIGESTS,DEPENDENCY-CHECK,VENDOR-CORES}.json,
evidence/AXIOMS.txt and evidence/AXIOMS-DEV-AUDIT.txt. FROZEN-STATEMENT.json is written by make_challenge.py.
"""
from pathlib import Path
import hashlib, json, re, subprocess, time

D = Path('/opt/uncomputable-noise-diagram-arxiv-2026-11-12')
P, O, E, R, K = D / 'project', D / 'original', D / 'evidence', D / 'results', D / 'kernels'
F = Path('/opt/forgetting-arxiv-2026-11-10')
U = Path('/opt/undecidable-phase-diagram-arxiv-2026-11-11')
DEV = Path('/opt/uncomputable-noise-diagram-lean')
E.mkdir(exist_ok=True)
COMMIT = 'ec67163'
ML = '56a005855ea17e0b0958f73ec801ae140b0a1679'
SESSION_START = '2026-11-11 23:00:00'   # WSL clock; staging began at 23:09
DEPS = ['plausible', 'LeanSearchClient', 'importGraph', 'proofwidgets', 'aesop', 'Qq', 'batteries', 'Cli', 'mathlib']
CORES = {'FixedNoiseErgodicity': F / 'project', 'UndecidablePhaseDiagram': U / 'project'}
FINAL = ['UND.theorem_A', 'UND.corollary_9_4', 'UND.one_rule_undecidable']


def sha_file(p):
    h = hashlib.sha256()
    with open(p, 'rb') as f:
        for b in iter(lambda: f.read(1 << 20), b''):
            h.update(b)
    return h.hexdigest()


def dump(name, obj):
    (E / name).write_text(json.dumps(obj, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')


version = subprocess.check_output([str(D / 'toolchain/bin/lean'), '--version'], text=True).strip()
mods = json.loads((P / 'scripts/modules.json').read_text())
pkg_mods = mods + ['Challenge', 'Solution', 'Audit']

# ---------------- BUILD.json
hist = [json.loads(l) for l in (P / '.lake/replay/history.ndjson').read_text().splitlines() if l.strip()]
end_first = next(i for i, r in enumerate(hist) if r['module'] == 'Audit' and r['exit'] == 0)
fresh, later = hist[:end_first + 1], hist[end_first + 1:]
final = {}
for r in hist:
    if r['exit'] == 0:
        final[r['module']] = r
core_mods = sorted({r['module'] for r in fresh if r['kind'] == 'core'})
cache = json.loads((P / '.lake/replay/completed.json').read_text())
missing = [m for m in pkg_mods if m not in final]
build = {
    'status': 'PASS' if not missing and all(r['exit'] == 0 for r in fresh) and all(m in cache for m in pkg_mods) else 'FAIL',
    'lean_version': version, 'mathlib_commit': ML,
    'source_commit': COMMIT,
    'clean_copy': 'project/ = git archive of the source commit (no build outputs), plus the package files; the two cores '
                  'vendored as sources under vendor/; no object of the development or of the cores was reused; '
                  'LEAN_PATH = this package\'s .lake/build/lib/lean and the nine pinned dependency packages only',
    'project_modules': len(mods), 'package_modules': len(pkg_mods), 'core_modules_compiled': len(core_mods),
    'core_modules': core_mods,
    'one_compiler_at_a_time': True, 'lean_heap_MiB': 5000, 'lean_threads': 1, 'timeout_seconds_per_module': 1800,
    'linux_process_tree_stop_rss_bytes': 9000000000,
    'peak_observed_tree_rss_bytes': max(r['peak_tree_bytes'] for r in hist),
    'minimum_available_before_build_bytes': min(r['free_before_bytes'] for r in hist),
    'memory_floor_bytes': 8 * 1024 ** 3,
    'module_options': {'UndecidablePhaseDiagram.Statements': ['-Dbackward.isDefEq.respectTransparency=false']},
    'records_note': 'Each peak is the cumulative process-tree peak of its replay invocation, hence an upper bound for '
                    'the module. free_before_bytes = min(Linux MemAvailable, Windows host heartbeat ullAvailPhys). '
                    'fresh_full_replay = one replay from an empty build directory (no --resume) of every module '
                    'reachable from the package roots; later_records = any module rebuilt afterwards.',
    'missing_modules': missing,
    'fresh_full_replay_records': len(fresh),
    'fresh_full_replay_all_exit_0': all(r['exit'] == 0 for r in fresh),
    'fresh_full_replay_seconds_total': round(sum(r['seconds'] for r in fresh), 3),
    'fresh_full_replay_warnings_total': sum(r.get('warnings', 0) for r in fresh),
    'fresh_full_replay_longest': max(fresh, key=lambda r: r['seconds'])['module'],
    'later_records': later,
    'final_by_module': {m: final[m] for m in [*core_mods, *pkg_mods] if m in final},
}
dump('BUILD.json', build)

# ---------------- COMPARATOR.json
cr = json.loads((R / 'comparator-receipt.json').read_text())
inv = [json.loads(l) for l in (D / 'bwrap-invocations.ndjson').read_text().splitlines() if l.strip()]
cfg = json.loads((P / 'comparator.json').read_text())
log = (R / 'comparator.log').read_text(errors='replace')
challenge = (P / 'Challenge.lean').read_text(encoding='utf-8')
cimps = re.findall(r'^import\s+(\S+)', challenge, re.M)
cr.update({
    'date_client': time.strftime('%Y-%m-%d'), 'mathlib_commit': ML,
    'comparator_command': 'lake comparator --config comparator.json',
    'theorem_names': cfg['theorem_names'], 'permitted_axioms': cfg['permitted_axioms'],
    'sandbox_observed': len(inv) > 0 and all('--unshare-all' in i['arguments'] for i in inv),
    'sandbox_invocations': len(inv),
    'sandbox_network_shared_invocations': sum('--share-net' in i['arguments'] for i in inv),
    'sandbox_invocation_commands': [i['arguments'][i['arguments'].index('--') + 1:] for i in inv],
    'default_kernel_accepts': 'Lean default kernel accepts the solution' in log,
    'comparator_verdict_line': 'Your solution is okay!' if 'Your solution is okay!' in log else None,
    'challenge_imports': cimps, 'challenge_imports_only_mathlib': all(i.startswith('Mathlib.') for i in cimps),
    'challenge_sha256': sha_file(P / 'Challenge.lean'), 'solution_sha256': sha_file(P / 'Solution.lean'),
    'transparent_definition_copy': True,
    'log': 'results/comparator.log', 'sandbox_invocation_log': 'bwrap-invocations.ndjson',
})
cr['status'] = 'PASS' if cr['exit'] == 0 and cr['default_kernel_accepts'] and cr['comparator_verdict_line'] and cr['sandbox_observed'] else 'FAIL'
dump('COMPARATOR.json', cr)

# ---------------- KERNEL-REPLAY.json
xr = json.loads((R / 'export-receipt.json').read_text())
kr = {'export_sha256': xr['sha256'], 'export_bytes': xr['bytes'], 'export_receipt': 'results/export-receipt.json',
      'export_command': xr['command'], 'export_lean_path': xr.get('lean_path'), 'export_seconds': xr['seconds'],
      'export_peak_tree_rss_bytes': xr['peak_tree_rss_bytes'], 'roots': xr['roots'], 'kernel_replays': {}}
for k in ('leanchecker', 'nanoda', 'nanoda-negative-control'):
    p = K / (k + '-receipt.json')
    if p.exists():
        kr['kernel_replays'][k] = json.loads(p.read_text())
kr['note'] = ('Both replays use the Linux binaries of the pinned toolchain (cp -a of the forgetting relay\'s toolchain, '
              'as in the hard-model relay). Each runs serially under the process-tree RSS watchdog (stop at 9.0 GB); '
              'neither tool has a memory-cap option. nanoda runs with num_threads 1 and a 128 MiB main-thread stack '
              '(RLIMIT_STACK), with the precedent relays\' axiom policy. The negative control reruns nanoda on the same '
              'export with Classical.choice not permitted and must be rejected.')
kv = kr['kernel_replays']
kr['status'] = 'PASS' if (kv.get('leanchecker', {}).get('exit') == 0 and kv.get('nanoda', {}).get('exit') == 0
                          and kv.get('nanoda-negative-control', {}).get('exit', 0) != 0) else 'FAIL'
dump('KERNEL-REPLAY.json', kr)

# ---------------- AXIOMS.txt / AXIOM-AUDIT.json
ax = (P / 'AXIOMS.txt').read_text(encoding='utf-8')
(E / 'AXIOMS.txt').write_text(ax, encoding='utf-8')
dev = (P / '.lake/replay/UncomputableNoiseDiagram.Audit.log').read_text(encoding='utf-8')
(E / 'AXIOMS-DEV-AUDIT.txt').write_text(dev, encoding='utf-8')


def decl_lines(tag):
    return [(lambda x: [x[0], x[1][0], x[1][1]])(json.loads(l.split(tag + ':', 1)[1]))
            for l in ax.splitlines() if l.startswith(tag + ':')]


und_decls, core_decls = decl_lines('UND_DECL'), decl_lines('CORE_DECL')
count = int(re.search(r'UND_DECL_COUNT:(\d+)', ax).group(1))
ccount = int(re.search(r'CORE_DECL_COUNT:(\d+)', ax).group(1))
roots = re.findall(r'^#print axioms (\S+)$', (P / 'Audit.lean').read_text(encoding='utf-8'), re.M)
std = {'propext', 'Classical.choice', 'Quot.sound'}
printed = dict(re.findall(r"^'?([^'\s]+)'? depends on axioms: \[([^\]]*)\]", ax, re.M))
final_axioms = {n: [a.strip() for a in printed.get(n, '').split(',') if a.strip()] for n in FINAL}
bad = [d for d in und_decls + core_decls if not set(d[2]) <= std]
errors = [l for l in ax.splitlines() if ': error' in l or 'error:' in l]
prefix_line = next((l for l in dev.splitlines() if l.startswith('audit_prefix UND')), None)
dump('AXIOM-AUDIT.json', {
    'status': 'PASS' if (not bad and not errors and count == len(und_decls) and ccount == len(core_decls)
                         and 'UND_FINAL_TYPES_OK' in ax and all(set(v) == std for v in final_axioms.values())) else 'FAIL',
    'run': 'fresh: the package Audit.lean was compiled in the fresh full replay (BUILD.json)',
    'permitted_axioms': sorted(std), 'final_theorem_axioms': final_axioms,
    'final_theorem_types_checked': 'UND_FINAL_TYPES_OK' in ax,
    'explicit_print_axioms_roots_count': len(roots),
    'development_declarations_count': count,
    'development_private_declarations': sum(1 for d in und_decls if d[0].startswith('_private')),
    'development_declarations_without_axioms': sum(1 for d in und_decls if not d[2]),
    'imported_core_declarations_count': ccount,
    'imported_core_modules': sorted({d[1] for d in core_decls}),
    'including_generated_and_private': True,
    'unexpected': bad, 'error_lines': errors,
    'dev_audit_prefix_line': prefix_line,
    'dev_audit_identical_to_committed_AXIOMS_txt': dev == (O / 'AXIOMS.txt').read_text(encoding='utf-8'),
    'dev_audit_note': 'evidence/AXIOMS-DEV-AUDIT.txt is the fresh output of UncomputableNoiseDiagram/Audit.lean '
                      '(1166 #audit_axioms_strict commands and #audit_prefix UND), compiled in the same replay.',
    'declarations': und_decls, 'core_declarations': core_decls,
    'axioms_text_sha256': sha_file(E / 'AXIOMS.txt'), 'source_census': 'SOURCE-AUDIT.json'})

# ---------------- SOURCE-AUDIT.json
lean_files = sorted([p for p in P.rglob('*.lean') if 'vendor' not in p.parts and '.lake' not in p.parts
                     and p.name != 'lakefile.lean'])


def strip_comments(text):
    """Blank out comments (nested /- -/, --) and string literals, keeping line structure (as sorry_census.py)."""
    out, i, n, depth = [], 0, len(text), 0
    while i < n:
        c = text[i]
        if depth == 0 and text.startswith('--', i):
            j = text.find('\n', i)
            j = n if j < 0 else j
            out.append(' ' * (j - i)); i = j; continue
        if text.startswith('/-', i):
            depth += 1; out.append('  '); i += 2; continue
        if depth > 0 and text.startswith('-/', i):
            depth -= 1; out.append('  '); i += 2; continue
        if depth > 0:
            out.append('\n' if c == '\n' else ' '); i += 1; continue
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            seg = text[i:j + 1]
            out.append(''.join('\n' if ch == '\n' else ' ' for ch in seg)); i = j + 1; continue
        out.append(c); i += 1
    return ''.join(out)
forb = re.compile(r'(^|[^`])(native_decide|implemented_by|@\[extern)|^[ \t]*axiom[ \t]|(^|[^`])autoImplicit[ \t]+true|decide[ \t]+\+native', re.M)
hits, sorries, noimp, mentions = [], [], [], []
for p in lean_files:
    t = p.read_text(encoding='utf-8')
    code = strip_comments(t)
    rel = str(p.relative_to(P))
    for m in forb.finditer(code):
        hits.append({'file': rel, 'line': code[:m.start()].count('\n') + 1, 'text': m.group(0).strip()})
    for m in re.finditer(r'(?<![\w.])sorry(?![\w])', code):
        sorries.append({'file': rel, 'line': code[:m.start()].count('\n') + 1})
    for m in re.finditer(r'\bsorry\b', t):
        ln = t[:m.start()].count('\n') + 1
        if not any(s['file'] == rel and s['line'] == ln for s in sorries):
            mentions.append({'file': rel, 'line': ln})
    if 'set_option autoImplicit false' not in t and rel != 'Solution.lean':
        noimp.append(rel)
ro = {}
for path in [F, Path('/opt/forgetting-arxiv-2026-11-10-runtime.tar.zst'), Path('/opt/forgetting-arxiv-2026-11-10-runtime.tar.json'),
             Path('/opt/package-forgetting-arxiv.py'), U, DEV]:
    out = subprocess.run(['find', str(path), '-newermt', SESSION_START, '-print'], capture_output=True, text=True)
    ro[str(path)] = out.stdout.split()
lint = subprocess.run(['bash', 'scripts/lint.sh'], cwd=P, capture_output=True, text=True)
census = subprocess.run(['python3', '-I', '-B', 'scripts/sorry_census.py'], cwd=P, capture_output=True, text=True)
dump('SOURCE-AUDIT.json', {
    'lean_files_checked': [str(p.relative_to(P)) for p in lean_files],
    'method': 'comments and string literals blanked out first (as scripts/sorry_census.py); lakefile.lean excluded',
    'forbidden_constructs': hits, 'sorry_tokens': sorries,
    'sorry_mentions_in_comments': mentions,
    'sorry_only_in_challenge_holes': all(s['file'] == 'Challenge.lean' for s in sorries) and len(sorries) == 3,
    'files_without_autoImplicit_false': noimp,
    'lint_sh_output': lint.stdout.strip(), 'lint_sh_exit': lint.returncode,
    'sorry_census_output': census.stdout.strip(),
    'read_only_inputs_modified_after_session_start': ro,
    'read_only_inputs_note': f'find -newermt "{SESSION_START}" (WSL clock; this session staged its workspace from 23:09) '
                             'over the forgetting relay, its runtime archive and receipt, its packaging script, the '
                             'hard-model relay and the development build folder: empty lists mean no file there was '
                             'created or modified during this session.',
})

# ---------------- CHOICES.json, ORIGINAL-SOURCE.json (source identity)
ch = []
for p in sorted(O.rglob('*.lean')):
    for i, l in enumerate(p.read_text(encoding='utf-8').splitlines(), 1):
        if '[choice]' in l:
            ch.append({'file': str(p.relative_to(O)), 'line': i, 'text': l.strip()})
dump('CHOICES.json', {'scope': f'Every [choice] occurrence in the development\'s Lean source (commit {COMMIT}). '
                      'F1-F24, FD1-FD2 and QB\'s rulings are in STATUS.md (unchanged); the release adds no fidelity choice.',
                      'count': len(ch), 'choices': ch})
orig = [{'path': str(p.relative_to(O)), 'sha256': sha_file(p)} for p in sorted(O.rglob('*')) if p.is_file()]
diff_in_project = [r['path'] for r in orig if not (P / r['path']).is_file() or sha_file(P / r['path']) != r['sha256']]
EXPECTED = {'AXIOMS.txt': 'replaced by the output of the package Audit.lean (scripts/replay.py copies it); the '
                         'development audit output of this replay is evidence/AXIOMS-DEV-AUDIT.txt'}
dump('ORIGINAL-SOURCE.json', {'commit': COMMIT, 'archive': 'source.tar (git archive of the commit)',
                              'archive_sha256': sha_file(D / 'source.tar'),
                              'project_files_identical_to_commit_except_expected': all(x in EXPECTED for x in diff_in_project),
                              'differences': diff_in_project, 'expected_differences': EXPECTED,
                              'files': orig})

# ---------------- BINARY-DIGESTS.json
recs = []
for b in ['lean', 'lake', 'leanexport', 'leanchecker', 'nanoda_bin']:
    p = D / 'toolchain/bin' / b
    recs.append({'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha_file(p),
                 'same_as_forgetting_relay_binary': sha_file(p) == sha_file(F / 'toolchain/bin' / b),
                 'same_as_hard_model_relay_binary': sha_file(p) == sha_file(U / 'toolchain/bin' / b)})
p = D / 'bubblewrap/usr/bin/bwrap'
recs.append({'path': str(p), 'bytes': p.stat().st_size, 'sha256': sha_file(p),
             'same_as_forgetting_relay_binary': sha_file(p) == sha_file(F / 'bubblewrap/usr/bin/bwrap'),
             'same_as_hard_model_relay_binary': sha_file(p) == sha_file(U / 'bubblewrap/usr/bin/bwrap')})
dump('BINARY-DIGESTS.json', {'records': recs, 'toolchain': 'cp -a of /opt/forgetting-arxiv-2026-11-10/toolchain (Lean 4.35.0, eb6cafb7290e8bd5f2937522d8d804f58f02bafc)'})

# ---------------- DEPENDENCY-CHECK.json (the nine pinned packages)
refp = F / 'evidence/DEPENDENCY-SOURCES.json'
ref = json.loads(refp.read_text())
listed = {f['path']: f for f in ref['files']}
mism = []
for path, f in listed.items():
    q = P / 'vendor' / path
    if not q.is_file() or q.stat().st_size != f['bytes'] or sha_file(q) != f['sha256']:
        mism.append(path)
unlisted = []
for d in DEPS:
    for q in (P / 'vendor' / d).rglob('*.lean'):
        rel = str(q.relative_to(P / 'vendor'))
        if '.lake' not in q.parts and rel not in listed:
            unlisted.append(rel)
hl = subprocess.run(['find', str(P / 'vendor'), '-type', 'f', '-links', '+1'], capture_output=True, text=True).stdout.split()
dump('DEPENDENCY-CHECK.json', {
    'expected_mathlib_commit': ML,
    'vendor_copy': 'cp -a of /opt/forgetting-arxiv-2026-11-10/project/vendor/<package> for the nine packages of lake-manifest.json',
    'hard_links_in_vendor': len(hl),
    'reference': str(refp) + ' (the forgetting relay\'s manifest; its model package compared the mathematical Mathlib '
                             'sources byte for byte with the official commit archive; published as lean/pins/'
                             'DEPENDENCY-SOURCES.json of the forgetting release v1.4.0)',
    'reference_sha256': sha_file(refp),
    'checked_dependency_source_files': len(listed), 'mismatches': mism,
    'unlisted_lean_source_files_outside_build_dirs': unlisted,
    'status': 'PASS' if not mism and not unlisted and not hl else 'FAIL',
})

# ---------------- VENDOR-CORES.json (the two reused cores)
rel_cores = json.loads((D / 'release-cores.json').read_text())
vc = {}
for name, src in CORES.items():
    V = P / 'vendor' / name
    files = sorted(q for q in V.rglob('*') if q.is_file())
    diffs = [str(q.relative_to(V)) for q in files if sha_file(q) != sha_file(src / q.relative_to(V))]
    # every file of the precedent workspace except vendor/, .lake/ and heartbeat files is present
    srcfiles = [q for q in src.rglob('*') if q.is_file() and q.relative_to(src).parts[0] not in ('vendor', '.lake')
                and q.name not in ('.host-memory.json', '.host-memory.stop')]
    absent = [str(q.relative_to(src)) for q in srcfiles if not (V / q.relative_to(src)).is_file()]
    rc = rel_cores[name]
    lean_rel = {k: v for k, v in rc['files'].items() if k.endswith('.lean')}
    cmp = {'identical': 0, 'different': [], 'absent_in_vendor': []}
    for k, h in lean_rel.items():
        q = V / k
        if not q.is_file():
            cmp['absent_in_vendor'].append(k)
        elif sha_file(q) == h:
            cmp['identical'] += 1
        else:
            cmp['different'].append(k)
    compiled = [m for m in core_mods if m.split('.')[0] == name]
    used_lean = [m.replace('.', '/') + '.lean' for m in compiled]
    olean_same = []
    for m in compiled:
        rel = m.replace('.', '/') + '.olean'
        a, b = P / '.lake/build/lib/lean' / rel, src / '.lake/build/lib/lean' / rel
        olean_same.append([m, b.is_file() and sha_file(a) == sha_file(b)])
    vc[name] = {
        'vendored_from': str(src), 'copy': 'rsync -a (cp -a semantics) excluding vendor/, .lake/ and the relay heartbeat files',
        'files': len(files), 'files_differing_from_source_workspace': diffs, 'source_files_absent': absent,
        'release': {k: rc[k] for k in ('release_repo', 'tag', 'tag_commit', 'head', 'lean_dir_clean')},
        'release_lean_files_compared': len(lean_rel), 'release_lean_comparison': cmp,
        'compiled_modules_from_vendored_sources': compiled,
        'compiled_module_sources_identical_to_release': all(k in lean_rel and lean_rel[k] == sha_file(V / k) for k in used_lean),
        'compiled_oleans_byte_identical_to_precedent_oleans': olean_same,
    }
vc['FixedNoiseErgodicity']['release_difference_note'] = (
    'The vendored tree is the forgetting relay workspace. Five of its files differ from the v1.4.0 release lean/ folder '
    'only in comments (the release removed internal reviewer references): Hypotheses.lean, Main.lean, '
    'Section2/Ergodic.lean, Three/Corner.lean, Three/CornerCheck.lean; none of them is compiled here. The full diff is '
    'evidence/VENDOR-FNE-vs-release-v1.4.0.diff. cache-tool/Requests.lean exists only in the release (outside the proof '
    'import closure). The release v1.4.0 has no git tag in the local release repository; its head commit is recorded.')
vc['UndecidablePhaseDiagram']['release_difference_note'] = (
    'Every Lean file of the v1.2.0 release lean/ folder is byte-identical in the vendored tree except '
    'relay/attempts/comparator-1-matcher-mismatch/Challenge.lean, a relay record that exists only in the release.')
dump('VENDOR-CORES.json', vc)
print('evidence written:', sorted(x.name for x in E.iterdir()))
print('BUILD', build['status'], 'COMPARATOR', cr['status'], 'KERNELS', kr['status'], 'UND decls', count,
      'core decls', ccount, 'bad', len(bad), 'DEPS', 'PASS' if not mism and not unlisted and not hl else 'FAIL')
