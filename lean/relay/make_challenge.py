"""Generate Challenge.lean from the frozen statement files (run in WSL with python3 -I -B).

Challenge.lean imports only Mathlib: the Mathlib imports of `FixedNoiseErgodicity/Statements.lean` and of
`UndecidablePhaseDiagram/Statements.lean`, the two files that `UncomputableNoiseDiagram/Statements.lean`
imports. It then contains, between BEGIN/END markers:
  1. verbatim excerpts of `FixedNoiseErgodicity/Statements.lean`: its option/section/namespace header and
     the two definitions the statements use, `FNE.flagLaw` and `FNE.WeakTendsto` (with their docstrings);
  2. verbatim excerpts of `UndecidablePhaseDiagram/Statements.lean`: its option/section/namespace header,
     the block "Section 2.2: Turing machines" (`UPD.Machine`, `State`, `Symbol`, `Cfg`, `step`, `start`,
     `run`, `HaltsOn`) and `UPD.Universal` (with its docstring);
  3. `UncomputableNoiseDiagram/Statements.lean` byte for byte, except its two import lines;
then the three holes of `Main.lean` with `sorry`. Each copy is preceded by `run_cmd ... setMainModule`
(as in both precedents) so that generated and private names agree with the development. The excerpt of
`UndecidablePhaseDiagram/Statements.lean` is elaborated with the option that file is compiled with
(`backward.isDefEq.respectTransparency = false`) and with `bootstrap.genMatcherCode = false`, inside a
`section` that restores both. Reason for the latter: within one file Lean reuses an identical
pattern-matching auxiliary ("matcher") made earlier in that file, keyed by this option, while each module
of the development starts with an empty matcher cache; `UPD.Machine.run` and `UND.CA.run` both match on
`0` / `t + 1`, so without it `UND.CA.run` would reuse `UPD.Machine.run.match_1` instead of making its own
`UND.CA.run.match_1` as in the development (the hard-model challenge met the same effect and used the same
option). The `FixedNoiseErgodicity` excerpts contain no pattern matching. In the same way Lean reuses an
auxiliary proof (`_proof_n`) with the same proposition made earlier in the same file, through the cache
`Lean.Meta.auxLemmasExt`, a local environment extension that is not stored in .olean files (so every module
starts with it empty) and is keyed by the proposition alone. Each copy is therefore preceded by
`run_cmd Lean.modifyEnv (fun env => Lean.Meta.auxLemmasExt.modifyState env fun _ => {})`, which empties it
as at the start of a separate module; without it `UND.CA.uniformLaw` reused `FNE.flagLaw._proof_1` instead of
making `UND.CA.uniformLaw._proof_1` as in the development (first comparator run: "Const does not match between
challenge and target 'UND.CA.uniformLaw'"). The script re-extracts every copy from the generated file and
checks it against the sources.
"""
from pathlib import Path
import hashlib, json, re

D = Path('/opt/uncomputable-noise-diagram-arxiv-2026-11-12')
P = D / 'project'
SRC = {
    'UND': P / 'UncomputableNoiseDiagram/Statements.lean',
    'FNE': P / 'vendor/FixedNoiseErgodicity/FixedNoiseErgodicity/Statements.lean',
    'UPD': P / 'vendor/UndecidablePhaseDiagram/UndecidablePhaseDiagram/Statements.lean',
}
REF = {
    'UND': D / 'original/UncomputableNoiseDiagram/Statements.lean',
    'FNE': Path('/opt/forgetting-arxiv-2026-11-10/project/FixedNoiseErgodicity/Statements.lean'),
    'UPD': Path('/opt/undecidable-phase-diagram-arxiv-2026-11-11/project/UndecidablePhaseDiagram/Statements.lean'),
}
FROZEN = {'FNE': '351c3058f66fc99235677f99d04f8b35af1d365f80153d9644c6b13d207b4879',
          'UPD': 'ef3ebe7fc60c792f1297dcf9a4596504f5a365de5e45012df84da227fa01482b'}
H = lambda s: hashlib.sha256(s.encode()).hexdigest()
text = {k: p.read_text(encoding='utf-8') for k, p in SRC.items()}
for k in text:
    assert text[k] == REF[k].read_text(encoding='utf-8'), f'{k} statement file differs from its reference'
for k, h in FROZEN.items():
    assert H(text[k]) == h, k
lines = {k: t.split('\n') for k, t in text.items()}


def span(k, first, last):
    """Lines first..last (inclusive, exact full-line matches, each unique) of file k."""
    L = lines[k]
    i = [n for n, l in enumerate(L) if l == first]
    j = [n for n, l in enumerate(L) if l == last]
    assert len(i) == 1 and len(j) == 1 and i[0] <= j[0], (k, first, last, i, j)
    return i[0], j[0]


def decl(k, prefix):
    """The docstring and the declaration starting with `prefix`, up to the next blank line."""
    L = lines[k]
    d = [n for n, l in enumerate(L) if l.startswith(prefix)]
    assert len(d) == 1, (k, prefix, d)
    i = d[0]
    while not L[i].startswith('/--'):
        i -= 1
        assert L[i] != '', (k, prefix)
    j = d[0]
    while L[j + 1] != '':
        j += 1
    return i, j


EXCERPTS = {
    'FNE': [('header: options, section, opens, namespace', span('FNE', 'set_option autoImplicit false', 'namespace FNE')),
            ('FNE.flagLaw', decl('FNE', 'def flagLaw ')),
            ('FNE.WeakTendsto', decl('FNE', 'def WeakTendsto '))],
    'UPD': [('header: options, section, opens, namespace', span('UPD', 'set_option autoImplicit false', 'namespace UPD')),
            ('Section 2.2: UPD.Machine, State, Symbol, Cfg, step, start, run, HaltsOn',
             span('UPD', '/-! ## Section 2.2: Turing machines -/', 'end Machine')),
            ('UPD.Universal', decl('UPD', 'def Universal '))],
}
FILE = {'FNE': 'FixedNoiseErgodicity/Statements.lean', 'UPD': 'UndecidablePhaseDiagram/Statements.lean',
        'UND': 'UncomputableNoiseDiagram/Statements.lean'}


def excerpt_lines(k):
    out, recs = [], []
    for what, (i, j) in EXCERPTS[k]:
        body = '\n'.join(lines[k][i:j + 1])
        b = f'-- BEGIN verbatim excerpt of {FILE[k]}, lines {i + 1}-{j + 1} ({what})'
        e = f'-- END verbatim excerpt of {FILE[k]}, lines {i + 1}-{j + 1}'
        out += [b, body, e, '']
        recs.append({'file': FILE[k], 'what': what, 'first_line': i + 1, 'last_line': j + 1,
                     'begin_marker': b, 'end_marker': e, 'sha256': H(body), 'text_utf8': body})
    return out, recs


# UND: everything but the import lines
U = lines['UND']
imp_idx = [n for n, l in enumerate(U) if l.startswith('import ')]
assert imp_idx == list(range(imp_idx[0], imp_idx[-1] + 1)) and len(imp_idx) == 2
assert [U[n] for n in imp_idx] == ['import FixedNoiseErgodicity.Statements', 'import UndecidablePhaseDiagram.Statements']
und_head = '\n'.join(U[:imp_idx[0]])
und_body = '\n'.join(U[imp_idx[-1] + 1:])
assert und_head + '\n' + '\n'.join(U[n] for n in imp_idx) + '\n' + und_body == text['UND']

imports = []
for k in ('FNE', 'UPD'):
    for l in lines[k]:
        if l.startswith('import ') and l not in imports:
            imports.append(l)
assert all(l.startswith('import Mathlib.') for l in imports), imports

fne_ex, fne_recs = excerpt_lines('FNE')
upd_ex, upd_recs = excerpt_lines('UPD')
M_U0 = '-- BEGIN verbatim copy of UncomputableNoiseDiagram/Statements.lean (the whole file except its two import lines)'
M_U1 = '-- END verbatim copy of UncomputableNoiseDiagram/Statements.lean'

header = '''/-
# Challenge (comparator) for the Lean core of "One noisy cellular automaton with an uncomputable
# noise diagram" (S. Douglas and N. Mghirbi, v1.1.0, Zenodo DOI 10.5281/zenodo.24152233)

This file imports only Mathlib (the Mathlib imports of the two reused statement files) and imports no
module of the development or of the reused cores. Between BEGIN/END markers it copies, byte for byte:
verbatim excerpts of `FixedNoiseErgodicity/Statements.lean` (its header lines and `FNE.flagLaw`,
`FNE.WeakTendsto`), verbatim excerpts of `UndecidablePhaseDiagram/Statements.lean` (its header lines, the
block "Section 2.2: Turing machines" with `UPD.Machine` and `UPD.Machine.HaltsOn`, and `UPD.Universal`),
and the whole of `UncomputableNoiseDiagram/Statements.lean` except its two import lines (which import
those two statement files). Nothing else defines a statement. The structural lines between the copies
only open and close sections and namespaces, select the module name under which the copied definitions
are recorded (`run_cmd ... setMainModule`, as in the two precedent challenges), empty Lean's per-file cache
of auxiliary proofs before each copy (`run_cmd ... auxLemmasExt`, as at the start of a separate module, so that
auxiliary proof names agree with the development; see `make_challenge.py`), and set two options for
the hard-model excerpt: `backward.isDefEq.respectTransparency = false` (the option its file is compiled
with in the development) and `bootstrap.genMatcherCode = false` (a fresh matcher cache, as in a separate
module; see `make_challenge.py`); both are restored by the enclosing `section`. The comparator checks
every constant of the three statements against the development. The three holes at the end are the
final theorems of `Main.lean`, with the same binders.
-/'''

parts = [header, '\n'.join(imports), '',
         '/-! ## 1. From the forgetting core: `FNE.flagLaw`, `FNE.WeakTendsto` -/', '',
         'section', '',
         'run_cmd Lean.modifyEnv (fun env => env.setMainModule `FixedNoiseErgodicity.Statements)',
         'run_cmd Lean.modifyEnv (fun env => Lean.Meta.auxLemmasExt.modifyState env fun _ => {})', '',
         *fne_ex,
         'end FNE', '', 'end', '', 'end', '',
         '/-! ## 2. From the hard-model core: `UPD.Machine`, `UPD.Machine.HaltsOn`, `UPD.Universal` -/', '',
         'section', '',
         'set_option backward.isDefEq.respectTransparency false',
         'set_option bootstrap.genMatcherCode false', '',
         'run_cmd Lean.modifyEnv (fun env => env.setMainModule `UndecidablePhaseDiagram.Statements)',
         'run_cmd Lean.modifyEnv (fun env => Lean.Meta.auxLemmasExt.modifyState env fun _ => {})', '',
         *upd_ex,
         'end UPD', '', 'end', '', 'end', '',
         '/-! ## 3. The statement file of this development -/', '',
         'run_cmd Lean.modifyEnv (fun env => env.setMainModule `UncomputableNoiseDiagram.Statements)',
         'run_cmd Lean.modifyEnv (fun env => Lean.Meta.auxLemmasExt.modifyState env fun _ => {})', '',
         M_U0, und_head, und_body.rstrip('\n'), M_U1, 'end', '',
         '/-! ## The three holes (the final theorems of `Main.lean`) -/', '',
         'run_cmd Lean.modifyEnv (fun env => env.setMainModule `Challenge)', '',
         'namespace UND', '',
         'theorem theorem_A : TheoremA := by sorry', '',
         'theorem corollary_9_4 : CorollaryNineFour := by sorry', '',
         'theorem one_rule_undecidable : OneRuleUndecidable := by sorry', '',
         'end UND', '']
out = '\n'.join(parts)

# ---- self-check: re-extract every copy from the generated text
o = out.split('\n')
for r in fne_recs + upd_recs:
    i, j = o.index(r['begin_marker']), o.index(r['end_marker'])
    assert '\n'.join(o[i + 1:j]) == r['text_utf8'], r['what']
    assert r['text_utf8'] in text['FNE' if r['file'].startswith('Fixed') else 'UPD']
i, j = o.index(M_U0), o.index(M_U1)
u_copy = '\n'.join(o[i + 1:j])
assert u_copy == und_head + '\n' + und_body.rstrip('\n')
assert out.count('sorry') == 3
for bad in ['native_decide', 'implemented_by', '@[extern', 'decide +native']:
    assert bad not in out, bad
assert not re.search(r'^\s*axiom\s', out, re.M)
(P / 'Challenge.lean').write_text(out, encoding='utf-8', newline='\n')

holes = ['theorem theorem_A : TheoremA', 'theorem corollary_9_4 : CorollaryNineFour',
         'theorem one_rule_undecidable : OneRuleUndecidable']
rec = {
    'challenge_sha256': H(out),
    'challenge_imports': [l.split()[1] for l in imports],
    'challenge_imports_only_mathlib': True,
    'statement_files': {FILE[k]: {'sha256': H(text[k]), 'reference': str(REF[k]),
                                  'identical_to_reference': True} for k in text},
    'und_statements_copy': {'what': 'whole file except its two import lines', 'sha256': H(u_copy),
                            'reconstruction_check': 'head + import lines + body == file (asserted)',
                            'byte_identical_to_source_except_imports': True},
    'excerpts': fne_recs + upd_recs,
    'und_statements_lean_utf8': text['UND'],
    'targets': [{'name': 'UND.' + h.split()[1], 'statement_utf8': h, 'source': 'Main.lean (namespace UND)',
                 'sha256': H(h)} for h in holes],
    'auxiliary_proof_cache': 'run_cmd Lean.modifyEnv (fun env => Lean.Meta.auxLemmasExt.modifyState env fun _ => {}) '
                             'before each copy: empties the local (not persisted) per-file cache of auxiliary proofs, as at the '
                             'start of a separate module; first comparator run failed on UND.CA.uniformLaw without it',
    'options': {
        'hard_model_excerpt': ['backward.isDefEq.respectTransparency = false (the option UndecidablePhaseDiagram/Statements.lean is compiled with)',
                               'bootstrap.genMatcherCode = false (fresh matcher cache, as in a separate module)'],
        'scope': 'both set inside a section that also encloses the excerpt; restored at its end',
    },
    'independence': 'Only Mathlib imports; byte-identical excerpts/copies checked against the sources; no type_of%; '
                    'generated/private names aligned by selecting the original module (setMainModule) while '
                    'elaborating each copy.',
}
(D / 'evidence').mkdir(exist_ok=True)
(D / 'evidence/FROZEN-STATEMENT.json').write_text(json.dumps(rec, indent=2, ensure_ascii=False) + '\n', encoding='utf-8')
print('Challenge.lean', len(out.encode()), 'bytes, sha256', rec['challenge_sha256'])
print('imports', rec['challenge_imports'])
for r in fne_recs + upd_recs:
    print('excerpt', r['file'], r['first_line'], r['last_line'], r['what'])
