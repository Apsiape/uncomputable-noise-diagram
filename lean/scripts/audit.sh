#!/usr/bin/env bash
# Axiom audit (inside WSL): build everything (serial, capped), then copy the log of
# UncomputableNoiseDiagram.Audit (the #print axioms / #audit_* output) to AXIOMS.txt and summarize.
set -euo pipefail
cd "$(dirname "${BASH_SOURCE[0]}")/.."
python3 -I -B scripts/build.py
python3 -I -B scripts/build.py --force UncomputableNoiseDiagram.Audit
cp .lake/logs/UncomputableNoiseDiagram.Audit.log AXIOMS.txt
echo "---- axiom audit summary ----"
grep -c "depends on axioms" AXIOMS.txt | sed 's/^/single-constant audits: /'
grep -E "error" AXIOMS.txt && { echo "AUDIT FAILED"; exit 1; } || true
grep -E "audit_prefix|depending on sorryAx" AXIOMS.txt || true
echo "AUDIT OK (errors: none)"
