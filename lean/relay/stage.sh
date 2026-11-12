#!/usr/bin/env bash
# Stage the release workspace /opt/uncomputable-noise-diagram-arxiv-2026-11-12 (session 11).
# Reads (never writes) the two precedent workspaces. Source archive on stdin: git archive of ec67163.
set -euo pipefail
D=/opt/uncomputable-noise-diagram-arxiv-2026-11-12
F=/opt/forgetting-arxiv-2026-11-10
U=/opt/undecidable-phase-diagram-arxiv-2026-11-11
test ! -e "$D" || { echo "REFUSE: $D exists"; exit 1; }
mkdir -p "$D/original" "$D/project/vendor" "$D/environment" "$D/results" "$D/kernels" "$D/evidence" "$D/attempts"
cat > "$D/source.tar"
tar -xf "$D/source.tar" -C "$D/original"
tar -xf "$D/source.tar" -C "$D/project"
echo "sources extracted"
cp -a "$F/toolchain" "$D/toolchain"
cp -a "$F/bubblewrap" "$D/bubblewrap"
echo "toolchain, bubblewrap copied"
for p in plausible LeanSearchClient importGraph proofwidgets aesop Qq batteries Cli mathlib; do
  cp -a "$F/project/vendor/$p" "$D/project/vendor/$p"
done
echo "pinned dependency tree copied"
# The two reused cores: cp -a semantics (rsync -a), without their own vendor/ (the same pinned tree,
# supplied once above), build outputs (.lake/; this package compiles the cores from these sources)
# and the host-memory heartbeat files of their relays.
rsync -a --exclude=/vendor --exclude=/.lake --exclude=/.host-memory.json --exclude=/.host-memory.stop \
  "$F/project/" "$D/project/vendor/FixedNoiseErgodicity/"
rsync -a --exclude=/vendor --exclude=/.lake --exclude=/.host-memory.json --exclude=/.host-memory.stop \
  "$U/project/" "$D/project/vendor/UndecidablePhaseDiagram/"
echo "cores vendored"
echo "hard links in vendor: $(find "$D/project/vendor" -links +1 -type f | wc -l)"
du -sh "$D/toolchain" "$D/project/vendor" "$D/project/vendor/FixedNoiseErgodicity" "$D/project/vendor/UndecidablePhaseDiagram"
sync
echo 1 > /proc/sys/vm/drop_caches
grep MemAvailable /proc/meminfo
echo STAGED
