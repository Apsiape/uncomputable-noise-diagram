"""Sorry census: every `sorry` token in the Lean sources of the project (comments and string
literals excluded), with its file, line and enclosing declaration. Also reports forbidden
constructs (`native_decide`, `implemented_by`, `@[extern]`, `axiom` declarations, `admit`).

Run from the project root (Windows or WSL): python -I -B scripts/sorry_census.py
Exit code 0 always; the counts are printed. `scripts/audit.sh` gives the axiom-level census
(declarations depending on `sorryAx`), which is the authoritative one.
"""
from pathlib import Path
import re, sys

P = Path(__file__).resolve().parents[1]
FILES = sorted([P / 'UncomputableNoiseDiagram.lean'] + list((P / 'UncomputableNoiseDiagram').rglob('*.lean')))
DECL = re.compile(r'^\s*(?:@\[[^\]]*\]\s*)?(?:private\s+|protected\s+|noncomputable\s+)*'
                  r'(theorem|lemma|def|abbrev|instance|example|structure)\s+([^\s:(\[{]*)')
FORBIDDEN = re.compile(r'\b(native_decide|implemented_by|admit)\b|@\[extern|^\s*axiom\s')


def strip(text):
    """Blank out comments (nested /- -/, --) and string literals, keeping line structure."""
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


total, rows, bad = 0, [], []
for f in FILES:
    lines = strip(f.read_text(encoding='utf-8')).split('\n')
    decl = '?'
    for k, line in enumerate(lines, 1):
        m = DECL.match(line)
        if m:
            decl = f'{m.group(1)} {m.group(2)}'
        if FORBIDDEN.search(line):
            bad.append(f'{f.relative_to(P)}:{k}: {line.strip()}')
        for _ in re.finditer(r'(?<![\w.])sorry(?![\w])', line):
            total += 1
            rows.append(f'{f.relative_to(P)}:{k}: in `{decl}`')
print(f'sorry census: {total} sorry token(s) in {len(FILES)} files')
for r in rows:
    print('  ' + r)
if bad:
    print(f'FORBIDDEN constructs: {len(bad)}')
    for b in bad:
        print('  ' + b)
else:
    print('forbidden constructs: none')
