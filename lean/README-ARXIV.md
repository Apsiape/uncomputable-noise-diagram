# One noisy cellular automaton with an uncomputable noise diagram: Lean 4.35 arXiv verification package

Pins: Lean 4.35.0 / eb6cafb7290e8bd5f2937522d8d804f58f02bafc; Mathlib 56a005855ea17e0b0958f73ec801ae140b0a1679
(vendored as nine path packages under `vendor/`, not in git). The relay's `REPORT.md` and `evidence/` contain the
results; `SCOPE.md` says what is formalized; `STATEMENT-READ.md` reads the statement file against v1.1.0.

`Challenge.lean` imports only Mathlib. It contains verbatim excerpts of the two reused statement files
(`FNE.flagLaw`, `FNE.WeakTendsto`; `UPD.Machine` with `HaltsOn`, and `UPD.Universal`) and the whole of
`UncomputableNoiseDiagram/Statements.lean` except its two import lines, followed by exactly three intended
holes: `UND.theorem_A : TheoremA`, `UND.corollary_9_4 : CorollaryNineFour`,
`UND.one_rule_undecidable : OneRuleUndecidable`. `Solution.lean` imports the proved final results
(`UncomputableNoiseDiagram.Main`). `comparator.json` permits only `propext`, `Classical.choice` and
`Quot.sound`. `Audit.lean` prints and strictly audits all 1,166 roots of `UncomputableNoiseDiagram/Audit.lean`,
checks the axioms of every imported declaration of the development and of the imported modules of the two
reused cores (private and generated ones included), and checks the types of the three final theorems.

Reused cores (byte-identical sources, compiled here): `vendor/FixedNoiseErgodicity` (the forgetting core,
release v1.4.0 of "Forgetting under noise is undecidable") and `vendor/UndecidablePhaseDiagram` (the
hard-model core, release v1.2.0 of "An uncomputable phase diagram at positive temperature for one classical
lattice model"). Each is the precedent relay's ported workspace without its own `vendor/` (the same pinned
tree, supplied once here) and without build outputs. `scripts/replay.py` compiles exactly the modules of
them that this package imports, into this package's `.lake/build/lib/lean`; `UndecidablePhaseDiagram/Statements.lean`
is compiled with `-Dbackward.isDefEq.respectTransparency=false`, as in its own release.

## Reproduce on the recorded Windows/WSL machine

The native Linux workspace is `/opt/uncomputable-noise-diagram-arxiv-2026-11-12` in the `lean-comparator` WSL
distribution (toolchain, bubblewrap and the nine dependency packages copied with `cp -a` from the forgetting
relay `/opt/forgetting-arxiv-2026-11-10`). Do not place it under `/home`, `/root` or `/tmp`: the standard
comparator sandbox masks those directories.

From Windows, start `host-memory-monitor.py` (workspace root) with `python -I -B` in a separate process; it writes
the live host-memory heartbeat `project/.host-memory.json` every 2 s and stops by itself on
`project/.host-memory.stop` or after its time limit. Every compiler, comparator, export and kernel run refuses to
start without a fresh heartbeat or below 8 GiB available (host and Linux); all compiles use `-j1 -M5000`, a 1800 s
timeout and a process-tree RSS watchdog (stop at 9.0 GB); one process at a time.

Within WSL, `cd /opt/uncomputable-noise-diagram-arxiv-2026-11-12/project`:

- Build from source (the needed core modules, the 74 modules of the development, `Challenge`, `Solution`,
  `Audit`): `python3 -I -B scripts/replay.py` (`--resume` skips modules whose source, imports and options are
  unchanged). The output of `Audit.lean` is written to `AXIOMS.txt`.
- Lint and census: `bash scripts/lint.sh`, `python3 -I -B scripts/sorry_census.py`.
- The sandboxed comparator with receipts: `python3 -I -B ../run-linux.py comparator` (exactly
  `lake comparator --config comparator.json`, with `COMPARATOR_BWRAP` pointing to the invocation recorder
  `../bwrap-record`; default sandbox and kernel; no supplied exports).
- The replay export: `python3 -I -B ../run-linux.py export` (leanexport of `Solution` for the three targets).
- The two kernel replays and the negative control: `python3 -I -B ../run-linux.py leanchecker`,
  `python3 -I -B ../run-linux.py nanoda`, `python3 -I -B ../run-linux.py nanoda-negative`.
- Generators and evidence: `python3 -I -B ../make_challenge.py`, `python3 -I -B ../make_audit.py`,
  `python3 -I -B ../make_evidence.py`.

Mathlib was not rebuilt from source: the dependency sources match the pinned manifest file by file
(`evidence/DEPENDENCY-CHECK.json`), and both standalone kernels replay the exported proof closure. The
development's working records (`STATUS.md`, `BLUEPRINT.md`; the session handoff note is not shipped) and its development scripts
(`scripts/build.py`, `env.sh`, `wsl.ps1`, `audit.sh`) are kept as they were at the source commit; the
development build used prebuilt core objects on `LEAN_PATH`, which this package does not.
