# Uncomputable phase diagram: Lean 4.35 arXiv verification package

Pins: Lean 4.35.0 / eb6cafb7290e8bd5f2937522d8d804f58f02bafc; Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679 (vendored as path packages under `vendor/`, not in git). The relay's `REPORT.md` and `evidence/` contain the results and limitations.

`Challenge.lean` imports only Mathlib and contains byte-identical copies of `Statements.lean` and `Hypotheses.lean` (after their import blocks), followed by exactly three intended theorem holes: `UPD.theorem_A (h1 : H1) (h2 : H2) : TheoremA`, `UPD.corollary_B (h1 : H1) (h2 : H2) : CorollaryB`, `UPD.existsUniversal : ExistsUniversal`. `Solution.lean` imports the proved final results (`UndecidablePhaseDiagram.Main`). `comparator.json` permits only `propext`, `Classical.choice` and `Quot.sound`. `Audit.lean` prints and strictly audits all 1,269 roots of `UndecidablePhaseDiagram/Audit.lean` and checks the axioms of every imported project declaration, including private and generated ones, and the types of the three final theorems.

One build option: `Statements.lean` (frozen, sha256 `ef3ebe7f…`) is compiled unchanged with `-Dbackward.isDefEq.respectTransparency=false` (see `scripts/replay.py`, `MODULE_OPTIONS`): Mathlib's `deriving Fintype` for its ten enumeration types fails at this pin under the Lean 4.35 default; Mathlib itself sets the same core option for the same derivation. The challenge elaborates its copy of `Statements.lean` with the same option (an explicit `set_option`, reset before the `Hypotheses.lean` copy).

The authoritative source is this directory. `HANDOFF.md`, `STATUS.md` and `BLUEPRINT.md` are the records of the pre-port development (sessions 1–11); the relay `REPORT.md` supersedes their pending port and packaging status.

## Reproduce on the recorded Windows/WSL machine

The native Linux workspace is `/opt/undecidable-phase-diagram-arxiv-2026-11-11` in the `lean-comparator` WSL distribution (toolchain, bubblewrap and vendored dependencies copied with `cp -a` from the forgetting relay `/opt/forgetting-arxiv-2026-11-10`). Do not place it under `/home`, `/root` or `/tmp`: the standard comparator sandbox masks those directories.

From Windows, start `host-memory-monitor.py` (in the workspace root) with `python -I -B` in a separate process; it writes the live host-memory heartbeat `project/.host-memory.json` every 2 s and stops by itself on `project/.host-memory.stop` or after 6 h. Every compiler, comparator, export and kernel run refuses to start without a fresh heartbeat or below 8 GiB available (host and Linux); all compiles use `-j1 -M6144`, a 1800 s timeout and a process-tree RSS watchdog; one process at a time.

Within WSL, `cd /opt/undecidable-phase-diagram-arxiv-2026-11-11/project` and set `PATH=/opt/undecidable-phase-diagram-arxiv-2026-11-11/toolchain/bin:$PATH`, `LEAN_NUM_THREADS=1`.

- Rebuild the project sources: `python3 -I -B scripts/replay.py` (`--resume` skips modules whose source, imports and options are unchanged).
- Lint: `bash scripts/lint.sh`.
- The actual sandboxed comparator with receipts: `python3 -I -B ../run-linux.py comparator` (exactly `lake comparator --config comparator.json`, with `COMPARATOR_BWRAP` pointing to the invocation recorder `../bwrap-record`; the default sandbox and kernel stay enabled; no supplied exports).
- The replay export: `python3 -I -B ../run-linux.py export` (leanexport of `Solution` for the three targets).
- The two independent kernel replays of that export: `python3 -I -B ../run-linux.py leanchecker` and `python3 -I -B ../run-linux.py nanoda`.
- Evidence: `python3 -I -B ../make_evidence.py` and `python3 -I -B ../preservation.py`.

A rebuild of Mathlib from zero was not performed: the dependency sources match the pinned manifest file by file (`DEPENDENCY-CHECK.json`), and both standalone kernels replay the exported proof closure. Nonfatal deprecation and style warnings are retained. No project or solution `sorry`, new axiom, `native_decide`, `implemented_by` or `extern` is present; the three challenge holes are intentional.
