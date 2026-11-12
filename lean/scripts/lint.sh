#!/usr/bin/env bash
# Reject forbidden constructs anywhere in the Lean sources (mentions inside `backticks` are fine),
# and require `set_option autoImplicit false` in every Lean file. (After the hard-model core's
# scripts/lint.sh.)
cd "$(dirname "${BASH_SOURCE[0]}")/.."
status=0
pat='(^|[^`])(native_decide|implemented_by|@\[extern)|^[[:space:]]*axiom[[:space:]]|(^|[^`])autoImplicit[[:space:]]+true|decide[[:space:]]+\+native'
if grep -rnE "$pat" --include='*.lean' UncomputableNoiseDiagram UncomputableNoiseDiagram.lean; then
  echo "LINT: forbidden construct found"; status=1
fi
for f in UncomputableNoiseDiagram.lean $(find UncomputableNoiseDiagram -name '*.lean'); do
  grep -q 'set_option autoImplicit false' "$f" || { echo "LINT: $f lacks 'set_option autoImplicit false'"; status=1; }
done
[ $status -eq 0 ] && echo "lint ok"
exit $status
