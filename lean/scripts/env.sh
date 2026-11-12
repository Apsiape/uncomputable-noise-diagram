# Environment for building inside the WSL distro `lean-comparator` (source this file).
# Release pin: Lean v4.35.0 (eb6cafb7290e8bd5f2937522d8d804f58f02bafc),
# Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679.
#
# Reused libraries are imported as prebuilt .olean trees on LEAN_PATH (read only; never rebuilt,
# never written):
#   * the forgetting core   /opt/forgetting-arxiv-2026-11-10/project          (FixedNoiseErgodicity.*)
#   * the hard-model core   /opt/undecidable-phase-diagram-arxiv-2026-11-11/project (UndecidablePhaseDiagram.*)
#   * the pinned vendor tree /opt/forgetting-arxiv-2026-11-10/project/vendor/* (Mathlib and deps)
# The toolchain and vendor tree are symlinks in /opt/uncomputable-noise-diagram-lean.
UND_ROOT=/opt/uncomputable-noise-diagram-lean
UND_PROJ="$UND_ROOT/project"
FNE_PROJ=/opt/forgetting-arxiv-2026-11-10/project
UPD_PROJ=/opt/undecidable-phase-diagram-arxiv-2026-11-11/project
export PATH="$UND_ROOT/toolchain/bin:$PATH"
LP="$UND_PROJ/.lake/build/lib/lean:$FNE_PROJ/.lake/build/lib/lean:$UPD_PROJ/.lake/build/lib/lean"
for d in "$UND_ROOT"/vendor/*/; do LP="$LP:${d}.lake/build/lib/lean"; done
export LEAN_PATH="$LP"
SP="$UND_PROJ:$FNE_PROJ:$UPD_PROJ"
for d in "$UND_ROOT"/vendor/*/; do SP="$SP:${d%/}"; done
export LEAN_SRC_PATH="$SP"
export LEAN_NUM_THREADS=1
