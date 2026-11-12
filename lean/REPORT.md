# Release package for the Lean core of "One noisy cellular automaton with an uncomputable noise diagram" (session 11, 11 Nov 2026)

The development at commit `ec67163` (sorry census 0) builds from a clean copy with Lean 4.35.0 (commit `eb6cafb7290e8bd5f2937522d8d804f58f02bafc`) and Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`. Its three final theorems passed an actual bubblewrap-sandboxed Linux comparator run, including the comparator's default-kernel replay. Two independent kernel replays, leanchecker and nanoda, accepted the fresh Solution export. Every declaration of the development, and of the imported modules of the two reused cores, uses only `propext`, `Classical.choice` and `Quot.sound`. `Statements.lean` is unchanged since session 1 (sha256 `b5c9e965…`). There was no push, no contact and nothing public.

The native workspace is `/opt/uncomputable-noise-diagram-arxiv-2026-11-12` in the `lean-comparator` WSL distribution. Its package files, evidence and relay records are committed in this repository (commit `c53e4fb`), which remains the source of truth.

An independent check outside the package: `#print axioms` was run separately with the pinned Lean 4.35.0. It gives `UND.theorem_A`, `UND.corollary_9_4` and `UND.one_rule_undecidable` as depending on `[propext, Classical.choice, Quot.sound]` only.

## Results

**Build from a clean copy: PASS.**
- **Source.** `project/` is `git archive ec67163` (no build outputs) plus the package files. The two reused cores are vendored as sources.
- **Replay.** One fresh serial replay, without `--resume`, compiled all 117 reachable modules:
  - the 40 imported core modules;
  - the 74 modules of the development;
  - `Challenge`, `Solution` and `Audit`.
- **Conditions.** Every compile ran alone with `lean -j1 -M5000`. Peak process-tree RSS was 4,231,589,888 bytes. All compiles exited 0.
- **Checks.** Lint ok. Sorry census 0.
- **Evidence:** `evidence/BUILD.json`, `ORIGINAL-SOURCE.json` and `SOURCE-AUDIT.json`.

**Comparator: PASS.**
- **Run.** The actual `lake comparator --config comparator.json` used the toolchain's lake, the default sandbox (bubblewrap 0.9.0) and the default kernel. It printed "Lean default kernel accepts the solution" and "Your solution is okay!".
- **Targets.** `UND.theorem_A`, `UND.corollary_9_4` and `UND.one_rule_undecidable`.
- **Permitted axioms.** `propext`, `Quot.sound` and `Classical.choice`.
- **Challenge.** `Challenge.lean` imports only Mathlib.
- **Earlier failure.** A first run failed on an auxiliary-proof naming artefact (`UND.CA.uniformLaw`). It was fixed in the challenge only (auxiliary command (d) below) and is preserved in `relay/attempts/`.
- **Evidence:** `evidence/COMPARATOR.json`, `relay/results/comparator.log` and `relay/bwrap-invocations.ndjson`.

**Kernel replays: PASS.**
- **Export.** The Solution export is 428,064,401 bytes, SHA-256 `772397a9863f43cc888928df1752790d8916015d9d69e8fdfe8239b56d11e73b`.
- **leanchecker.** `leanchecker --from-export` accepted it.
- **nanoda.** `nanoda_bin` accepted it, with permitted axioms `propext`, `Classical.choice` and `Quot.sound`.
- **Negative control.** The same nanoda run without `Classical.choice` permitted is rejected.
- **Evidence:** `evidence/KERNEL-REPLAY.json` and `relay/kernels/`.

**Axioms: PASS, run fresh.**
- **Package audit.** It audits all 1,166 roots, the 3,712 imported declarations of the development (including the private and generated ones) and the 4,452 declarations of the 40 imported core modules. There is no axiom declaration, and only `propext`, `Classical.choice` and `Quot.sound` occur.
- **Types.** The three final theorems have exactly the types `UND.TheoremA`, `UND.CorollaryNineFour` and `UND.OneRuleUndecidable`.
- **Development audit.** The rerun of the development audit is byte-identical to the committed `AXIOMS.txt`.
- **Evidence:** `evidence/AXIOMS.txt`, `AXIOM-AUDIT.json` and `AXIOMS-DEV-AUDIT.txt`.

**Statement eye-read: faithful** (`STATEMENT-READ.md`). Every deviation from the printed wording is an accepted rendering choice (F1–F14) or a strengthening. One point is to be stated in the paper: Theorem 9.3's automaton (6) and intervals (17) are existential in the checked statement. The proof's witnesses are `UND.theCA U`, `UND.Param.loF` and `UND.Param.hiF`.

**Dependencies: PASS.**
- All 10,268 dependency source files match the pinned manifest published with the forgetting release v1.4.0.
- The toolchain and bubblewrap binaries are byte-identical to those used by both earlier releases.
- **Evidence:** `evidence/DEPENDENCY-CHECK.json` and `BINARY-DIGESTS.json`.

## The vendored cores

**Sources.**
- `vendor/FixedNoiseErgodicity` and `vendor/UndecidablePhaseDiagram` are copies of the earlier relay workspaces. Their own `vendor/`, their `.lake/` and their heartbeat files are excluded.
- Every compiled core source is byte-identical to the released Lean cores: forgetting v1.4.0 (DOI 10.5281/zenodo.24126025) and hard-model v1.2.0 (DOI 10.5281/zenodo.24144192).

**Build outputs.** All 40 rebuilt `.olean` files are byte-identical to the earlier ones.

**Differences from the release folders.**
- Five uncompiled forgetting files differ from the v1.4.0 release folder only in comments.
- **Decision (QB, 12 Nov 2026):** a public `lean/` folder ships the released v1.4.0 tree. `vendor/` is not committed; it is fetched as in the hard-model release.

## The challenge

`Challenge.lean` contains:
- verbatim excerpts of the forgetting statement file (`FNE.flagLaw`, `FNE.WeakTendsto`);
- verbatim excerpts of the hard-model statement file (`UPD.Machine` and its run and halting definitions, `UPD.Universal`);
- the whole of this development's `Statements.lean` except its imports;
- three holes.

Excerpts are used because whole copies would collide on generated matcher names.

The auxiliary commands:
- (a) `setMainModule` before each copy, as in both earlier releases;
- (b) `set_option backward.isDefEq.respectTransparency false` for the hard-model excerpt;
- (c) `set_option bootstrap.genMatcherCode false` for the hard-model excerpt;
- (d) a reset of Lean's per-file auxiliary-proof cache (`Lean.Meta.auxLemmasExt`) before each copy. This reproduces the empty cache of a separate module.

**Decision (QB, 12 Nov 2026):** (d) is accepted. It affects only generated proof names. Because the comparator compares every constant reachable from the three statements with the development, a discrepancy can only cause a failure, never a false acceptance.

## QB decisions (12 Nov 2026)

1. The challenge's auxiliary command (d) is accepted, as above.
2. Theorem 9.3 is existential (row T0). The paper's Lean appendix states this. A named, proof-side theorem `NoiseDiagram U (theCA U) loF hiF` will be added with the appendix.
3. The proof-route differences F21 (Lemma 8.4 through the raw marked set, with no rare-birth contours), F22 (Lemma 8.3 not used) and F23 (block-indexed packing in Lemma 8.2) are accepted. They will be described in the appendix with F17 and F19.
4. The next paper version adds a Lean appendix, in the style of the hard-model paper's Appendix D. It is built from the audited names, `SCOPE.md` and this report, and it notes that the typical-phase routing existence is a proved import (D34).
5. The released forgetting v1.4.0 tree is shipped. `vendor/` is fetched, not committed.
6. Minor: the 3 exponent-threshold notices in `Parameters/Search.lean` remain. The frozen `Statements.lean` header keeps its v1.0.0 citation, so that its recorded sha256 stays fixed; its Theorem A, Theorem 9.3 and Corollary 9.4 are printed identically in v1.1.0.

## Layout and reproduction

**In this repository:**
- the package files: `Challenge.lean`, `Solution.lean`, `Audit.lean`, `comparator.json`, `lakefile.lean`, `lake-manifest.json` and `README-ARXIV.md`;
- `scripts/` (`replay.py`, `resource_guard.py`, `modules.json`);
- `REPORT.md`, `SCOPE.md` and `STATEMENT-READ.md`;
- `evidence/`;
- `relay/` (scripts, results, kernels, attempts and the sandbox invocation log).

**Not in git:** `vendor/` (6.8 GB), the `.lake/` objects and the 428 MB export. They stay in the WSL workspace.

`README-ARXIV.md` gives the reproduction commands.
