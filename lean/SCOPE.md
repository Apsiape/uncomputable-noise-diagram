# Scope of the Lean formalization

This development formalizes, in Lean 4.35.0 with Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`,
**Theorem A** of S. Douglas and N. Mghirbi, "One noisy cellular automaton with an uncomputable noise
diagram", v1.1.0 (Zenodo DOI 10.5281/zenodo.24152233), in its form **Theorem 9.3**, and
**Corollary 9.4**, end to end. `UND.theorem_A : UND.TheoremA`, `UND.corollary_9_4 : UND.CorollaryNineFour`
and the one-rule corollary `UND.one_rule_undecidable : UND.OneRuleUndecidable` (the sentence after
Theorem A) are proved from the frozen statement file `Statements.lean`. The proofs contain no `sorry`
and take no named hypotheses. They use no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.
Every step of Sections 2–8 and of the parameter verification of Section 9 that these results use is
proved.

**Not formalized:**
* Corollary B (the fixed interaction on `ℤ⁷`);
* Theorems 9.5–9.7 (exponential all-input coalescence, continuum many extremal states, field response)
  and the finite-history Appendix A that serves them;
* Theorem B.1 (the robustness radius);
* Corollaries 9.8–9.12;
* the scale remark, Remark 9.13 (the Chernoff alternative for the scales), and the numerical scale
  report of Section 9 (`verification/scale_check.py`);
* two printed intermediate claims that Theorem A does not use: the clause "any other positive count
  eventually fails" of Lemma 4.1(b) (F16), and Lemma 8.3 (F22).

The statements are held as printed, but four proof routes differ from the text:
* **F17.** Proposition 4.3's translation-invariant chart law is the Haar pushforward along
  `τ ↦ chartOf τ`, not a weak limit of spatial averages of one chart.
* **F19.** Lemmas 7.2 and 8.4 keep every group link of the copied-arm witness and count them linearly
  (`≤ 25g`), instead of extracting the printed star sub-witness (`5g`). The encodings still feed exactly
  the printed union bounds: `≤ 256g` edges against `K_mem`, and `≤ 512g` edges against `K_rare`.
* **F21.** Lemma 8.4 bounds a live `A_t` by the raw marked set `𝓜` (through Lemma 8.2), not by the
  rare-birth field of Lemma 8.3. It covers discrepancy paths with Lemma 5.2's raw contours, at most
  `101f ≤ 512f` edges into `K_rare^f`, with base `K_rare ε < 1`. The Lean proof of Lemma 8.4 therefore
  avoids rare-birth contours, and v1.1.0's correction (iv), the birth-contour clock, is not exercised.
* **F23.** Lemma 8.2's packing of historical queries is indexed by blocks with Hölder weights (the
  printed exponents, block weights summing to `β^r`, `β < 1`), instead of the printed
  `(f + m₀)`-indexed count.

The notes F17–F24 in `STATUS.md` record these differences and the intermediate strengthenings (F18).
The paper's construction parameters, including `k = 52386`, are used unchanged.

**Reused cores.** Two cores are on the same pins. The release package vendors them as sources under
`vendor/` and compiles from source exactly the modules this development imports: 4 modules of the
forgetting core and 36 of the hard-model core. Each of these sources is byte-identical to the released
Lean core, and each rebuilt object is byte-identical to the one built in that core's own verification
workspace. The comment-only differences in five unused files of the vendored forgetting tree are in
`evidence/VENDOR-CORES.json`. The cores are:
* the forgetting core `FixedNoiseErgodicity`, from "Forgetting under noise is undecidable" v1.4.0
  (DOI 10.5281/zenodo.24126025). It supplies the statement-level `FNE.flagLaw` and `FNE.WeakTendsto`
  and the Section 2 process and edge-count layers.
* the hard-model core `UndecidablePhaseDiagram`, from "An uncomputable phase diagram at positive
  temperature for one classical lattice model" v1.2.0 (DOI 10.5281/zenodo.24144192). It supplies
  `UPD.Machine`, `UPD.Machine.HaltsOn`, `UPD.Universal`, the universal machine
  `UPD.Compiler.univMachine_universal`, and the scaffold, tower and background-chart layers. The chart's routing
  fields are its `UPD.BG.cfg` unchanged (D34).
