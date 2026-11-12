# Lean formalization: Theorem A, Corollary 9.4 and the one-rule corollary

This directory proves, in Lean 4 with Mathlib, Theorem A of "One noisy cellular automaton with an uncomputable noise diagram" (in the existential form of Theorem 9.3), Corollary 9.4, and the one-rule corollary stated after Theorem A. The proofs contain no `sorry` and take no named hypotheses, and they use no axioms beyond Lean's three standard axioms `propext`, `Classical.choice` and `Quot.sound`. Appendix C of the paper describes the formalization: its exact scope, the proof-route differences and the recorded checks.

## What is proved

`UncomputableNoiseDiagram/Statements.lean` defines, transparently and with no proofs of substance, every object that occurs in the three statements, and states them as propositions. The proofs are in `UncomputableNoiseDiagram/Main.lean` and the modules it imports.

| Printed result | Lean name |
|---|---|
| Theorem A, in the form of Theorem 9.3 | `UND.theorem_A : UND.TheoremA` |
| Corollary 9.4 | `UND.corollary_9_4 : UND.CorollaryNineFour` |
| The one-rule corollary after Theorem A | `UND.one_rule_undecidable : UND.OneRuleUndecidable` |

`SCOPE.md` lists what is and is not formalized. `STATEMENT-READ.md` reads the statement file against the paper, row by row.

## Checks

- **Pins:** Lean 4.35.0 (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.
- **Comparator:** `Challenge.lean` imports only Mathlib and states the three targets as holes. `comparator.json` permits only the three standard axioms. The sandboxed `lake comparator` run accepted `Solution.lean`.
- **Kernel replays:** two independent kernels, leanchecker and nanoda, replayed the exported proof closure. A negative control, nanoda without `Classical.choice` permitted, was rejected as expected.
- **Axiom audit:** `Audit.lean` checks the axioms of every declaration of the development and of the imported modules of the reused cores. The result is in `AXIOMS.txt`.
- **Records:** `REPORT.md` gives the full results, and `evidence/` the machine-readable records. `relay/` holds the run logs.

## Reused cores

The development imports parts of two earlier Lean cores, compiled from their public sources:
- the forgetting core: the `lean/` folder of "Forgetting under noise is undecidable", version 1.4.0, DOI [10.5281/zenodo.24126025](https://doi.org/10.5281/zenodo.24126025);
- the hard-model core: the `lean/` folder of "An uncomputable phase diagram at positive temperature for one classical lattice model", version 1.2.0, DOI [10.5281/zenodo.24144192](https://doi.org/10.5281/zenodo.24144192).

## Reproduction

`README-ARXIV.md` gives the recorded setup and commands, as run on a Linux (WSL) workspace. The Mathlib dependencies and the two reused cores are placed under `vendor/` as path packages; they are fetched, not shipped. The pinned dependency versions are recorded in `lake-manifest.json`. `scripts/replay.py` compiles the needed core modules, the development, `Challenge`, `Solution` and `Audit`, one process at a time.

The working records of the development (`STATUS.md`, `BLUEPRINT.md`) are kept as they were at the source commit.

## License

The Lean sources are released under the Apache License 2.0. See the repository root for the licenses of the other files.
