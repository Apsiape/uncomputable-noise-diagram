#!/usr/bin/env bash
# Install the package files (tar on stdin) into the staged release workspace and generate the
# module list, Challenge.lean and the package Audit.lean.
set -euo pipefail
D=/opt/uncomputable-noise-diagram-arxiv-2026-11-12
U=/opt/undecidable-phase-diagram-arxiv-2026-11-11
cd "$D"
tar -xf - -C "$D" --no-same-owner
cp -a "$U/project/scripts/resource_guard.py" "$D/project/scripts/resource_guard.py"
cp -a "$U/linux_guard.py" "$U/bwrap-record" "$D/"
sed 's/"name": "UndecidablePhaseDiagram",/"name": "UncomputableNoiseDiagram",/' "$U/project/lake-manifest.json" > "$D/project/lake-manifest.json"
grep -c '"name": "UncomputableNoiseDiagram"' "$D/project/lake-manifest.json"
python3 -I -B - <<'PY'
from pathlib import Path
import json
P = Path('/opt/uncomputable-noise-diagram-arxiv-2026-11-12/project')
mods = ['UncomputableNoiseDiagram'] + sorted(
    str(p.relative_to(P).with_suffix('')).replace('/', '.') for p in (P / 'UncomputableNoiseDiagram').rglob('*.lean'))
(P / 'scripts/modules.json').write_text(json.dumps(mods, indent=2) + '\n')
print('modules', len(mods))
PY
python3 -I -B make_challenge.py
python3 -I -B make_audit.py
ls -la "$D" "$D/project" "$D/project/scripts"
