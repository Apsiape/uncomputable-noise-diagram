# Blueprint: Lean core of "One noisy cellular automaton with an uncomputable noise diagram"

Paper: S. Douglas and N. Mghirbi, v1.0.0, 11 Nov 2026, Zenodo DOI 10.5281/zenodo.24147269
(read-only source: `C:/Infanox/uncomputable-noise-diagram-release/paper/main.tex`, `main.pdf`, 28 pp;
`verification/scale_check.py`). Session 1, 11 Nov 2026; statuses updated in sessions 2–10 (same day).
(Version 1.1.0 is released, DOI 10.5281/zenodo.24152233, with Theorem A, 9.3, 9.4 byte-identical;
QB, s10: Section 8 and the history base are read from v1.1.0; the formal targets match v1.1.0.)
**Session 10: the core is complete (sorry census 0; the three final theorems use only `propext`,
`Classical.choice`, `Quot.sound`).**

**Core** = Theorem 9.3 (`thm:main`, printed in Section 9; Theorem A of the introduction) and
Corollary 9.4 (`cor:undecidable`), exactly as printed. `Statements.lean` states them as
`UND.TheoremA` and `UND.CorollaryNineFour` (plus `UND.OneRuleUndecidable`, the sentence after
Theorem A with a universal machine supplied); `Main.lean` holds `UND.theorem_A` (**DONE, s10**:
`UND.Memory.theoremA_of_halting UND.Forget.halting_branch`), `UND.corollary_9_4` and
`UND.one_rule_undecidable` (both DONE from `theorem_A`).
**Corollary B (the `ℤ⁷` Gibbs statement) is NOT in the core**; Part H says how it would enter.

Conventions (as in the two earlier cores): estimates are in agent turns (one tool round trip with
a Lean check); one session is about 20–30 turns. Risk: L (routine), M (needs care or design),
H (long or mathematically delicate in Lean). Status: DONE (proved, strict audit), STMT (defined in
`Statements.lean`), TODO. Kind: **REUSE** (an existing, audited declaration of the forgetting core
`FNE` or the hard-model core `UPD`, used as is through the import), **ADAPT** (an existing proof is
the template; it is generalized or re-instantiated, with a provenance note), **NEW** (written here),
**NAMED HYPOTHESIS** (a published theorem of other authors entering as an explicit hypothesis;
none is planned for the core, see Part C).

Paper numbering (checked against `main.pdf`): Prop 2.1 `prop:local`; Prop 3.1 `prop:scaffold`,
Lemma 3.2 `lem:cutoff`, Lemma 3.3 `lem:allphase`; Lemma 4.1 `lem:machine`, Lemma 4.2 `lem:input`,
Prop 4.3 `prop:chart`; Lemma 5.1 `lem:pole`, 5.2 `lem:rawpaths`, 5.3 `lem:coherence`, 5.4
`lem:deep`; Lemma 6.1 `lem:ownership`, 6.2 `lem:tails`, 6.3 `lem:joint`; Lemma 7.1
`lem:decomposition`, 7.2 `lem:memorycount`, Theorem 7.3 `thm:memory`; Lemma 8.1 `lem:miss`, 8.2
`lem:eliminate`, 8.3 `lem:rare`, 8.4 `lem:fullcoupling`, 8.5 `lem:pullback`; Lemma 9.1
`lem:counts`, Prop 9.2 `prop:parameters`, Theorem 9.3 `thm:main`, Corollary 9.4
`cor:undecidable`. Equations: (1) geometry, (2) alphabet, (3) drivers, (4) helper fields,
(5) `Pin`, (6) proposal, (7) frames, (8) rank filter, (9) lane phase, (10) tableau, (11) pole
constants, (12) pole bound, (13) span count, (14)/(15) upper/lower laws, (16) characteristics,
(17) windows, (18) ruler margins, (19) joint bound, (20) `Q`-law, (21) compression, (22) history
bases, (23) group noise, (24) count constants, (25) `B`-search, (26) rare constants, (27) `ε_*`,
(28) `n₀`-search.

---

## Part A. Dependency graph

The proof of Theorem 9.3 (Section 9) uses: Prop 2.1 and Prop 9.2 (the rule is fixed and
computably specified), Theorem 7.3 (nonhalting), Lemmas 8.4 and 8.5 (halting), and the window
arithmetic of (17). Corollary 9.4 uses Theorem 9.3 and the computability of the midpoints. The
layers below are listed bottom-up; "uses" lists direct dependencies.

```
                       Thm 9.3 ──────────────► Cor 9.4 (DONE from Thm 9.3)
              ┌───────────┼──────────────────────┐
         Thm 7.3       Lem 8.4 ─► Lem 8.5      windows (17) DONE, Prop 9.2, Prop 2.1
        /   |   \      /  |  \        \
  Lem 7.1 Lem 7.2 P4  Lem 8.3 8.2 5.1  P6,P8,P9
    |       |  \        |    / | \
 Lem 6.3  Lem 5.1 9.1  5.2  8.1 5.4 5.3 ─────────────────┐
  /  \                       |                           |
6.1  6.2                  Prop 4.3 ◄── Lem 4.2, 4.1, 3.3, 3.2 ◄── Prop 3.1 (UPD scaffold, REUSE)
                              ▲
                     rule (2)–(6), chart R, machine P
```

Critical path (longest chain of H nodes): rule definitions (A.2) → chart alphabet `R` with routing
(A.3 S7) → **Lemma 3.3** (all-phase board forcing) and **Lemma 4.1** (machine `P`) → **Prop 4.3**
→ (halting) **Lemma 5.3** (coherence) → **Lemma 8.2** (packing) → **Lemma 8.3** → **Lemma 8.4**
(full coupling, uses **Lemma 5.1**) → Lemma 8.5 → Theorem 9.3. The nonhalting branch (Sections 6–7)
runs in parallel and shares Lemma 5.1, Lemma 9.1 and the PCA layer A.1.

### A.0 Statements (Section 2 definitions, Theorem 9.3, Corollary 9.4)

| node | Lean | kind | status |
|---|---|---|---|
| CA on `ℤ^d`, finite alphabet, finite neighbourhood, local rule (Section 2) | `UND.Site`, `UND.CA`, `CA.Sym`, `CA.Config`, `CA.apply` | NEW | STMT |
| uniform whole-symbol replacement; process; law; stationary; ergodic | `CA.uniformLaw`, `CA.Noise`, `CA.noiseLaw` (flags `FNE.flagLaw`), `CA.update`, `CA.run`, `CA.law`, `CA.IsStationary`, `CA.IsErgodic` (weak convergence `FNE.WeakTendsto`) | NEW (shape of FNE `run`/`law`/`IsInvariant`/`IsErgodic`); REUSE `FNE.flagLaw`, `FNE.WeakTendsto` | STMT |
| translation invariance; two TI stationary laws | `CA.shift`, `CA.IsTranslationInvariant`, `CA.HasTwoTIStationaryLaws` | NEW | STMT |
| two-sided noise, pullbacks, "eventually a singleton" (Lemma 8.5, Thm 9.3 last clause) | `CA.Noise₂`, `CA.noiseLaw₂`, `CA.flow`, `CA.pullback`, `CA.PullbackEventuallySingleton` | NEW | STMT |
| universal machine `U`, halting on positive unary inputs | `UPD.Machine`, `UPD.Machine.HaltsOn`, `UPD.Universal`, `UPD.ExistsUniversal` | REUSE (hard-model statements) | STMT |
| computable disjoint rational open intervals | `UND.Presents`, `UND.window`, `UND.IsWindowFamily` | NEW (presentation as in `UPD.CorollaryB`) | STMT |
| Theorem 9.3 / Theorem A | `UND.NoiseDiagram`, `UND.TheoremA` | NEW | STMT |
| Corollary 9.4 | `UND.PromiseUndecidable`, `UND.CorollaryNineFour`, `UND.OneRuleUndecidable` | NEW | STMT |
| Cor 9.4 from Thm 9.3 (midpoint `ε_n`) | `UND.midP`, `computable_midP`, `promiseUndecidable_of_noiseDiagram`, **`corollaryNineFour_of_theoremA`**, **`oneRuleUndecidable_of_corollary`** (with `UPD.Compiler.univMachine_universal`) (`Corollary.lean`) | NEW | **DONE (s1)** |

### A.1 The PCA layer (Section 2, used by Thm 7.3 and Lemma 8.5)

The forgetting core proves all of this for its quorum rule `F^[k]_R` on `ℤ² × ℤᵏ`
(`FixedNoiseErgodicity/Section2/*.lean`); its statements are hard-wired to that rule, so the proofs
are ported once to a generic local rule on a countable site set with a finite alphabet (D3).

| node | planned Lean | kind (template) | turns | risk | uses |
|---|---|---|---|---|---|
| P1 noise laws are probability measures (`0 ≤ ε ≤ 1`) | **`UND.CA.isProbabilityMeasure_noiseLaw`**, `isProbabilityMeasure_noiseLaw₂`, `isProbabilityMeasure_uniformLaw`, `isProbabilityMeasure_noiseSite` (`PCA/Process.lean`) | REUSE `FNE.isProbabilityMeasure_flagLaw`; ADAPT `FNE.isProbabilityMeasure_noiseLaw` | – | – | **DONE (s1)** |
| P2 locality, measurability of `apply`/`run`; `law μ t` probability; `law μ 0 = μ`; mixture formula; flag cylinders `ε^{|Σ|}` | **`apply_congr`**, `measurable_of_local`, `measurable_apply`, **`measurable_run`**, `isProbabilityMeasure_law`, `law_zero`, `law_apply_eq_lintegral`, `law_dirac`, `noiseLaw_flags_eq` (`PCA/Process.lean`) | ADAPT `FNE.measurable_of_local`, `measurable_run`, `law_apply_eq_lintegral`, `noiseLaw_flags_eq` | – | – | **DONE (s1)**; continuity (`continuous_run`, template `FNE.continuous_of_local`) moves to P4 |
| P3 Markov property, one-step product form, positive rates | **`law_succ`**, `law_succ'`, **`law_dirac_one`**, `siteLaw`, `siteLaw_pos`, `noiseLaw_map_splitN`, `run_succ_shift` (`PCA/Markov.lean`) | ADAPT `FNE.law_succ`, `law_succ'`, `noiseLaw_map_splitN`, `law_dirac_one`, `siteLaw_pos` | – | – | **DONE (s1)** |
| P4 Feller; Cesàro limits are stationary; a stationary law exists; weak convergence iff cylinders iff window TV | **`continuous_Phi`**, `exists_cesaro_limit`, **`isStationary_of_cesaro_limit`**, **`exists_stationary`**, `weakTendsto_iff_cyl`, `weakTendsto_iff_dtv`; cylinders, `dtv`, `deltaO`, `Forgets` (`PCA/Cylinder.lean`, `PCA/Feller.lean`) | ADAPT `FNE.continuous_Phi`, `exists_cesaro_limit`, `isInvariant_of_cesaro_limit`, `exists_invariant`, `weakTendsto_iff_cyl`, `weakTendsto_iff_dtv` | – | – | **DONE (s2)** |
| P5 translation invariance: `apply` commutes with shifts; TI initial law ⇒ TI laws and Cesàro averages; weak limits of TI laws are TI | **`apply_shift`**, `run_shift`, `noiseLaw_map_shiftNoise`, **`law_map_shift`**, `isTI_law`, `isTI_cesaro`, `isTI_of_weakTendsto`, **`isTI_of_cesaro_limit`** (`PCA/Translation.lean`) | NEW | – | – | **DONE (s2)** |
| P6 forgetting ⇒ ergodic (`δ_O(t) → 0`); coupling bound | **`ergodic_of_forgets`**, `dtv_law_le`, `law_of_stationary` (`PCA/ForgetErgodic.lean`); NEW **`dtv_law_dirac_le`**, `deltaO_le_disagree`, **`forgets_of_coupling`** (`PCA/Cylinder.lean`) | ADAPT `FNE.ergodic_of_forgets`, `dtv_law_le`, `law_of_invariant` | – | – | **DONE (s2)** |
| P7 cylinder separation ⇒ two distinct laws; memory ⇒ not ergodic | `HasMemoryFrom` (two initial laws), **`two_stationary_of_memory`**, **`hasTwoTIStationaryLaws_of_memory`** (Thm 7.3, last paragraph), `not_ergodic_of_two`, `not_ergodic_of_memoryFrom`, `noiseDiagram_clauses` (the three clauses of `NoiseDiagram` at one rate from the two branches) | ADAPT `FNE.two_invariant_of_memory`, `not_ergodic_of_memory` | – | – | **DONE (s2)** |
| P8 time homogeneity of the two-sided noise: pullback failure probability = forward coupling failure probability | `tau`, **`noiseLaw₂_map_tau`**, `flow_eq_run`, **`noiseLaw₂_pullFail`**; finite cone `run_congr_cone`, `measurableSet_disagree` (`PCA/Attraction.lean`) | NEW | – | – | **DONE (s2)** |
| P9 complete trajectories; `K_j` nested compact; `⋂ K_j` = time-0 states of complete trajectories; finite projections stabilize | `IsComplete`, `pullback_mono`, **`exists_complete_of_pullback`**, `exists_complete`, **`pullback_eventually_singleton_of_unique`** (`PCA/Pullback.lean`) | NEW | – | – | **DONE (s2)** |

### A.2 The rule (Section 2: (1)–(6), Prop 2.1)

| node | planned Lean | kind | turns | risk | uses |
|---|---|---|---|---|---|
| geometry (1): `m, L, K, q, h`, `T`, clusters `S_i`, `2h > q` | `UND.Param.m … h`, `q_lt_two_h`, `q_sub_h`, `two_h_sub_q`, `clusterOffset`, `IsBlockOffset` | NEW | – | – | **DONE (s1)** `Parameters/Geometry.lean` |
| R1 chart letters `𝓛_R = (3×3 legal block, bit)`, `𝒜_R = {⊥} ∪ 𝓛_R`, compatibility at Moore displacements, checked providers | `UND.Rule.WangRel`, `IsLegalBlock`, `LiveLetter`, `ChartSym`, `Compatible`, `IsFullChart`, `Keeps`, `chk`, `chk_translate`, `chk_congr` (`Rule/Checker.lean`) | ADAPT `FNE.Compatible`, `FNE.CheckerKeeps`, `FNE.checker` (D4, D18) | – | – | **DONE (s3)** |
| R2 the quorum checker `F_R` over `q` providers in five clusters; uniqueness of the quorum letter; a cloned legal chart is fixed | `Prov`, `card_Prov`, `provOff`, **`FR`**, **`quorum_unique`**, `FR_eq_some_iff`, `FR_eq_none_iff`, **`FR_cloned`**, `FR_translate`, `FR_local`, `FR_iter_translate`, **`FR_iter_local`** (`Rule/Checker.lean`) | ADAPT `FNE.quorumRule`, `quorum_unique`, `quorumRule_translate` | – | – | **DONE (s3)** |
| R3 helper alphabet `ℋ` (LOW, UNKNOWN, 98 HIGH), represented intervals; `Σ = 𝒜_R × 𝒜_R × ℋ^B` (2) | `Ival`, `Helper`, `Helper.rep`, `Ival.repr`, `Helper.rep_repr`, `Helper.card_rep`, `PhysSym` (`Rule/Proposal.lean`) | NEW (D19) | – | – | **DONE (s3)** |
| R4 drivers (3) `A_t`, `Q_t = F_R^T(D_{t-1})(u, P - (T-1)v)`; fields (4); `Pin` (5); proposal (6) | `ChartData`, `drvA`, `drvQ`, `Jof`, `Jf`, `hcount`, `lcount`, `Pin`, **`proposal`**, **`proposal_translate`**, **`proposal_local`**, `nbhdP`, **`card_nbhdP_le`** (`Rule/Proposal.lean`) | NEW (generic in the tile set; the concrete `R` and its tile functions come from A.3) | – | – | **DONE (s3)** |
| R5 **Prop 2.1**: (6) is one finite-range CA; `κ = 2B(n_A + n_Q + 2)` parents; alphabet `Fin |Σ|` through `Fintype.equivFin`, `ℤ⁶ ≅ ℤ² × ℤ⁴` | `siteEquiv`, `caOf`, **`caOf_apply`**, `card_nbhd_caOf`, `ruleCA`, `ruleCA_apply`, **`prop_2_1`** (`Rule/CA.lean`) | NEW (D20) | – | – | **DONE (s3)**; `theCA U := ruleCA (chartData U) sParam` once S7 gives the concrete `R` |
| R6 the noisy automaton read in `Σ` and `ℤ² × ℤ⁴`; uniform replacement mark; uniform helper fields ("(2) is a product") | `update_decode`, `uniformLaw_decode`, `card_field_fiber`, **`uniformLaw_field`** (`Rule/Noise.lean`) | NEW | – | – | **DONE (s3)** (single-coordinate marginals; joint independence is `Measure.infinitePi` on the automaton side) |

### A.3 Charts, frames and routing (Section 3)

| node | planned Lean | kind | turns | risk | uses |
|---|---|---|---|---|---|
| S1 **Prop 3.1** (scaffold facts): injective expansion-two substitution; legality both ways; unique desubstitution tower | `UPD.Scaffold.Letter.child_injective`, `legalOn_phi'_iff`, `desub`, `exists_tower_of_tiling`, `tower_unique` | REUSE | – | – | DONE in UPD |
|  quarter tilings: unique offset `δ` and phase `τ = δ + 2ϖ`; every phase occurs; residue mod `2^l` local | `quarter_exists`, `quarter_unique`, `IsQPhase`, `IsQPhase.unique`, `qphase_shift`, `qphase_local`, `exists_phase`, `isQTiling_qshift` | REUSE | – | – | DONE in UPD |
|  Haar-a.e. phase: tiling determined, finite ranks, every coordinate in a finite frame | `ae_typical`, `Typical`, `quarter_ti_a`, `Typical.inFrame_col/row`, `quarter_ti_law`, `quarter_phase_haar` | REUSE | – | – | DONE in UPD |
|  frames (7): disjoint/strictly nested; deeper contains shallower; free coordinates, `N_d = 2^{d+2} - 2`, extremes | `frameLo`, `frameHi`, `InFrame`, `phaseOffsets`, `FrameOffsets`, `frames_nested`, `frames_contain`, `endpoint_not_inFrame`, `IsFree`, `card_free`, `isFree_rfree`, `isFree_frameHi_sub_one`, `Laminar.*` | REUSE | – | – | DONE in UPD |
|  finite-rank walls and ruler bits (all tilings; one axis finite) | `red_col`, `red_row`, `walls_col`, `walls_row` (parent tower), `rank_bits_col`, `rank_bits_row` | REUSE | – | – | DONE in UPD |
|  wiring: physical (quarter) coordinates, `z = δ_i + 2u + σ`, parent rank `ν₂(u - ϖ_i)`; finite-rank wall classification on quarters, in every phase | **`UND.Chart.walls_VW_of_rank`**, **`walls_HW_of_rank`** (`Chart/Walls.lean`) | ADAPT `UPD.Scaffold.walls_VW/HW` without `NotInt` (D23) | – | – | **DONE (s3)** |
| S2 black-type rank comparison (paragraph after Prop 3.1) | **`UND.Chart.black_rank_compare`**, `chain_black`, `black_child_*` | NEW | – | – | **DONE (s1)** `Chart/BlackType.lean` |
| S3 rank flags `V`, `H_row` and filter (8); decorated parents; quartering of the decorated alphabet | `UND.Chart.rankOK`, `DTriple`, `DLetter`, `DQuarter` (Wang colours), `matchE_iff`, `matchN_iff`, `toQ`, `isQTiling_toQ`, `H_row_const`, `V_col_const` (`Chart/Decorated.lean`) | NEW (D26) | – | – | **DONE (s4)** |
| S4 **Lemma 3.2** (cutoff): one common nonincreasing `(b_r)`; every finite cutoff occurs over every typical chart | abstract part `cutoff_of_filter`, `exists_rank` (s1); wiring **`cutoff_of_dtiling`** (every phase), **`cutoff_exists`** (phase coordinates not integers) (`Chart/Decorated.lean`) | NEW | – | – | **DONE (s4)** |
| S5 lane phase (9) as a finite higher-block extension; `p(Bot_d(z')) ≡ (4z'+1)4^d (mod 4^{min(d+1,k)})`; phase-zero gates on finite bottom rows of depth `d` iff `d ≥ k` (**FD2**: restricted form, CONFIRMED s4) | arithmetic (s3): `lanePhase`, `lanePhase_bot`, **`lanePhase_bot_eq_zero_iff`**; decoder (s4, D7, D25): `winRad`, `Word`, `wordAt`, `phaseTable`, **`phaseTable_wordAt`** (`Chart/PhaseTable.lean`); on legal charts **`IsRChart.phase_eq`**, **`IsRChart.gate_iff`** (`Chart/RChart.lean`) | NEW (decoder from `UPD.Scaffold.qphase_local`, D7) | – | – | **DONE (s4)** |
| S6 `Orig`, `End`; origins/ends `(L_d(z), Bot_d(z'))`, `(R_d(z), Bot_d(z'))`; `ℓ_d = 2·4^d - 1` | `frameHi_sub_frameLo` (s3); `IsOrig`, `IsEnd`, **`bottom_corner_iff`**, **`orig_iff`**, **`end_iff`** (one finite rank suffices), **`end_gate`** (`Chart/Origins.lean`) | NEW | – | – | **DONE (s4)** |
| S7 routing (O1)–(E3), logical colours, records, flags, tableau (10); the finite alphabet `R` (tuples passing the tests + phase extension) | `ContentOps`, `RVal`, `O1 … E3`, `K1`, `K2`, `C0`, `Tab`, `K3`, `Allowed`, `RTile`, `TileE`, `TileN`, **`chartData`** (`Chart/Routing.lean`); `contentP`, `theCAOf`, **`theCA`**, **`prop_2_1_theCAOf`**, **`theoremA_of_theCA`** (`Chart/TheCA.lean`); legal charts `IsRChart`, **`word_apply`** (`Chart/RChart.lean`) | ADAPT the shapes of `UPD.SiteVal.O1 … K3, C0`; NEW content (D24–D26) | – | – | **DONE (s4)** |
| S8 **Lemma 3.3** (finite-board forcing in every phase): closed frame has finite ranks `≤ 2d`; free rows carry exactly the two end walls; strip orientation `(L,R)`; vertical carriers = interiors of minimal members of a finite laminar family; event tags give the exact flags; colours/records give the recursion `s_{i+1}(j) = f_P(…)` | **`exists_prank_le_of_inFrame`** (`Chart/Origins.lean`); **`board_row(_walls)`**, **`board_col(_walls)`**, **`board_active`** (`Chart/Board.lean`); `exists_gap`, **`laminar_gap`**, **`board_not_vcarrier`**, **`board_not_hcarrier`** (`Chart/BoardGaps.lean`); **`board_flags_row`**, **`board_flags_col`** (`Chart/BoardFlags.lean`); **`board_record`**, **`board_init`**, **`board_step`**, **`board_vlink`**, `board_bottom`, `board_top` (`Chart/BoardTableau.lean`). indexed packaging (s5, `Chart/BoardRun.lean`): `FreeOff`, **`count_freeOff`**, `freeAt` (`Nat.nth`), **`board_run`** (record at `(x_i, y_j)` carries `runP i j`) | NEW (frame lemmas REUSED from UPD) | – | – | **DONE (s4)** as building blocks; **indexed DONE (s5)** |

### A.4 The computation carried by a chart (Section 4)

| node | planned Lean | kind | turns | risk | uses |
|---|---|---|---|---|---|
| M1 machine `P` (tracks `h_in, π, z, p_*, e_*, n_*, u_*`; SCAN … RUN, HALT, FAIL); `S_P`; ordered `f_P` | `UND.MachineP.Tape`, `Cont`, `PState`, `program`, `deltaP`, `Cell`, `fromBelow`, `fromAbove`, **`fP`**, `initP`, `CarriesHalt` (`Machine/P.lean`) | NEW (shape of `UPD.programM`, `fM`; choices D28) | – | – | **DONE (s4)** |
| M2 **Lemma 4.1**(a): `f_P` = sequential `P` with one head; exits fail | **`nextRow_stay/up/down(_fail)`**, **`nextRow_colOf`**, **`runP_eq`**, `stepB_iterate(_eq)` (`Machine/Run.lean`) | ADAPT `UPD.MachineM.nextRow_*`, `nextRow_colOf`, `runM_eq` | – | – | **DONE (s5)** |
| M3 **Lemma 4.1**(b): `j_* + 2 = 2^e`, parity guard, `e` even passes, APPENDN/SKIP/FINDN/APPENDU, RUN = `U(e - n₀ - 1)` | `Machine/Scan.lean` (forgetting the input tracks, SCAN, **`scan_guard`**, RUN simulates `U`: **`sim_halts`**, **`sim_no_halt`**), `Machine/Passes.lean` (**`pass_blocks`**, **`halving_step`**, **`skip_phase`**, **`copy_step`**, **`reaches_run`**), `Machine/Decode.lean` (**`decode_halts`**, **`decode_no_halt`**, **`guard_no_halt`**, **`runP_halts`**, **`runP_no_halt`**) | NEW (template `UPD.MachineM` `Run.lean`) | – | – | **DONE (s5)** (D29: the non-power failure clause is not needed and not formalized; D30) |
| M4 **Lemma 4.2** (which input is read): ranks of free coordinates (noncentral zero or odd, centre `2d`); `|A_a| = 2^{a+1}`; initial zero index `2^{a+1} - 2` | **`prank_left/center/right`**, **`free_left_rank`**, **`free_rank_even`**, **`initial_zero`**, **`count_initial_zero`**, `chi2_eq`, **`input_read_large`**, **`input_read_small`** (`Chart/Input.lean`) | NEW (template `UPD.Scaffold.card_free`, `sum_allowed`) | – | – | **DONE (s5)**, every phase |
| M5 **Prop 4.3**, nonhalting: a TI law of legal charts with either bit and cutoff `2a-2` or `2a-1` (typical phase; orientation/event assignment of DMhard Props 5.1, 5.7, Lemma 5.3; boards filled with runs; Haar phase) | `Chart/NonHalting.lean` (s5: `board_no_halt`, `board_run_no_halt`); `Chart/Construct.lean` (s6: `dqOf_spec`, `HSegM`…, `sAt`, `raw_rules` (tableau (10)), `raw_allowed`, **`chartOf`**, **`chartOf_isRChart`**, `chartOf_phase`, `chartOf_V/H`, **`chartOf_bottom_flag`**); `Chart/ChartLaw.lean` (s6: covariance, **`chartOf_shift`**, D31 **`measurableSet_typical`**, **`haar_typical`**, `measurable_chartOf`, `chartLaw`, **`chartLaw_shift`**, `ae_goodChart`, **`chart_law_exists`**) | ADAPT `UPD.BG.cfg` (routing fields verbatim, D34), `cfg_O1 … cfg_E3`, `cfg_active`, `cfg_grids_c`, `HSeg_unique`, `PhaseSystem.isTILaw`, `ae_typical_addDig`, `MLevel`; NEW covariance (D32) | – | – | **DONE (s6)** (D31, D32, D34); the global bit enters with the live-letter lift (Mem1) |
| M6 **Prop 4.3**, halting: every legal chart in every phase has a wrong flag at depth `a-1` or `a` | **`chart_wrong_flag`**, `bottomEnd_gate` (`Chart/Halting.lean`) | NEW | – | – | **DONE (s5)**, every phase |

### A.5 Contour estimates (Section 5)

| node | planned Lean | kind | turns | risk | uses |
|---|---|---|---|---|---|
| potentials (11): sum zero; good gains `160`, `ϱ₊ = 85`; worst `-715`; `A₀ = 4000/85 < 48` | `UND.Param.psi0`, `psiI`, `psi_sum`, `gain_zero_good`, `gain_i_good`, `gain_zero_worst`, `gain_i_worst`, `A0_eq` | NEW | – | – | **DONE (s1)** |
| C1 **Lemma 5.1** (grouped terminal estimate): finite root-reachable acyclic support graph, binary nonterminals with five good supports, unary zero-potential links, terminal groups with oscillation `≤ Ω`; `e ≤ A₀(g-1) + Ωg/ϱ₊`; span `≤ e`; singleton groups give `≥ 2` flags | `UND.Contour.GroupedSystem`, `IsPotential`, `exists_bij`, **`grouped_terminal_estimate`**, **`grouped_terminal_estimate_paper`** ((12) with five charges, 85, 715), `witness`, **`witness_connected`**, `singleton_two_le`, **`witness_span`** (`Contour/Grouped.lean`) | ADAPT `FNE.Contour.SupportSystem` (frontier `Rel W`, `exists_poles`, `exists_bij`, `meas`) to groups, unary links, rank-acyclicity and inequality potentials; REUSE `FNE.EdgeCount.ConnectedAt`, `Reach` | – | – | **DONE (s2)**, abstract form; the instances are built in C2, C4, Mem3, F4 |
| C2 **Lemma 5.2** (raw paths): `𝓜^{t₀}`, `𝓜`; no infinite backward path in `𝓜`, a.s., all roots | `Contour/RawPaths.lean`: **`sys`** (the marked derivation as a `GroupedSystem`), **`exists_contour`**, **`exists_cover`**, `measure_le_tsum_from`, **`raw_paths`**, **`raw_paths_threshold`** | NEW (D35) | – | – | **DONE (s7)** |
| C3 **Lemma 5.3** (coherence): unmarked live readings equal over providers (induction on provider separation, injective pairing (13)); Moore compatibility; `V_t + Mo ⊆ V_{t-1}`; full legal time-constant chart | `Contour/Coherence.lean`: **`exists_pair`** (13), `sep_step`, `IsFlagTraj`, `MClosed`, `UL`, **`coh_rel`**, **`coherence_eq`**, **`coherence_compat`**, `coh_back`, `coh_cover`, **`coherent_chart`**, `marked` (𝓜), **`marked_closed`**, **`isFlagTraj_of_complete`**, **`coherence_complete`** | NEW (D33) | – | – | **DONE (s6)** |
| C4 **Lemma 5.4** (deep wrong readings): virtual levels, characteristic coordinates, `f ≥ 11`, span bound | `Contour/Deep.lean`: **`sysD`**, **`exists_deep_contour`**, **`deep_wrong`**, **`deep_wrong_lag`** | NEW (D36) | – | – | **DONE (s7)** |

### A.6 Noise sensors (Section 6)

| node | planned Lean | kind | turns | risk | uses |
|---|---|---|---|---|---|
| N1 ideal interval fields; laws (14) `p̄_d = .99[1-(1-ε)^{ℓ_d}]`, (15) `p_W = .98[1-(1-ε)^W]` | `Sensors/Ideal.lean`: **`infinitePi_inter_eq_mul`**, `RideEv`, **`rideEv_real`**, **`upper_law`**, **`lower_law`** (D38); the ride's atoms `ride` (s8) | NEW | – | – | **DONE (s7, s8)** |
| N2 **Lemma 6.1** (ownership): characteristics (16), disjoint source supports, independent lanes | `Sensors/Ownership.lean`: **`infinitePi_biInter_eq_prod`**, **`iIndepFun_of_detBy`**, `chSite`, `laneAtom`, `ride`, `IsGate`, **`phaseZero_block`**, **`ownership`**, **`gateAtoms_disjoint`**; `Sensors/Gate.lean`: `lanes_iIndep` (D39) | NEW | – | – | **DONE (s8)** |
| N3 **Lemma 6.2** (intrinsic tails): Chernoff (exponential moment) and Hoeffding for Bernoulli sums; numerics `log(75/53) ≥ 11/32`, `.75·11/32 - .22 > .03`, `.75 log 4 - .3975 > 1/3`, `21/40·128/127 < .53`, `.98(1-e^{-.99C}) > .9C`; sums `3u_B/(1-4z_B) + 2w_B` | `Sensors/Tails.lean` (s7: **`short_tail`**, **`long_tail`**, …); `Sensors/Gate.lean` (s8: **`ShortBad`**, **`LongBad`**, **`shortBad_le`**, **`longBad_le`**); `Sensors/Joint.lean` (s8: `card_ends_le`, **`statEv_le`**) (D37, D40) | NEW (Mathlib `measure_ge_le_exp_mul_mgf`, `HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`) | – | – | **DONE (s7, s8)** |
| N4 **Lemma 6.3** (joint source bound) `γ = √C + η̂_B^{1/6}`: disjoint atoms, residue classes mod 3, Cauchy–Schwarz mixing | `Sensors/Joint.lean`: **`joint_bound`** (abstract), `RawEv`, `StatEv`, **`statSupp_disjoint`**, **`joint_source_bound`**; `Sensors/Selected.lean`: **`regime_final`**, **`joint_source_final`** (D40) | NEW | – | – | **DONE (s8)** |

### A.7 Memory when `U(n)` does not halt (Section 7)

| node | planned Lean | kind | turns | risk | uses |
|---|---|---|---|---|---|
| Mem1 the initial law: correct cutoff chart, a bit lift, helpers in their stationary chart-driven law (negative-time noise), spatial average with Haar phase | `Memory/RefChart.lean` (`liftChart`, **`liftChart_full`**, **`chart_gate`**), `Memory/Init.lean` (`firstHit`, **`initField_rec`**, `X0`, **`hyb`**, **`hyb_hyp`**), `Memory/InitLaw.lean` (**`measurable_X0`**, **`initLaw_TI`**, **`glue_law`**, **`law_initLaw`**), `Memory/Theorem.lean` (`memLaw`, **`memLaw_TI`**) | NEW (D42, D44, D45) | – | – | **DONE (s9)** |
| Mem2 **Lemma 7.1** (error decomposition) | the helper ride (s8, `Memory/Ride.lean`); the derivation (s9, `Memory/Derivation.lean`: **`sysM`**, **`exists_pgood`**, **`isPotential_sysM`**, **`term_source`**) | NEW (D43) | – | – | **DONE (s8, s9)** |
| Mem3 **Lemma 7.2** (counting memory witnesses): projection to characteristic coordinates, `≤ 48(g-1)` positive edges, `< 256g` edges, degree `Δ`, `≤ K_mem^g` | core (s8, `Memory/Count.lean`); instance (s9: `fM`, `nbrM`, **`card_nbrM_le`**, **`step_nbr`**, **`mem_cover`**; `Memory/Error.lean`: **`joint_MP`**, **`mem_bad_le`**) | NEW (D41, F19) | – | – | **DONE (s8, s9)** |
| Mem4 **Theorem 7.3** (two stationary laws): `Σ(K_mem γ)^g < 1/4`, cylinder `> 3/4`, Feller/Cesàro, TI, distinct | `Memory/Theorem.lean`: **`law_initLaw_le`**, **`memory_branch`**, **`theorem_7_3`**, **`theoremA_of_halting`** | NEW (D46) | – | – | **DONE (s9)** |

### A.8 Forgetting when `U(n)` halts (Section 8)

| node | planned Lean | kind | turns | risk | uses |
|---|---|---|---|---|---|
| F1 **Lemma 8.1** (missed-erasure implication), per complete trajectory | `Forget/Miss.lean`: **`helperTraj_of_complete`** (s9), monotone rides **`ride_mono`**, **`ride_mono_short`**, **`lcount_le_short`**, **`lo_le_hcount`**, **`missed_erasure`**; `Forget/Gate.lean`: **`isRChart_ctr`**, **`halting_gate`** (D47, F24) | NEW | – | – | **DONE (s10)** |
| F2 **Lemma 8.2** (excluding unmarked liveness): path at a wrong critical end; Hölder weight `ε^{3f/4}ρ_B^{m₀/4}`; bases (22) | `Forget/History.lean`: **`measure_WEv_le`**, **`tsum_wt_le`**, **`exists_witness`**, **`hpath_null`**; `Forget/Eliminate.lean`: **`uld_back`**, **`node_prop`**, **`hpath_of_ul`**, **`no_ul_generic`** (D48, D49, F23) | NEW | – | – | **DONE (s10)** |
| F3 **Lemma 8.3** (rare births) | not formalized: unused under the route F21 (F22) | – | – | – | **not needed (s10)** |
| F4 **Lemma 8.4** (full-state discrepancies) | `Forget/Coupling.lean`: **`proposal_of_dead`**, **`live_marked`**, **`disc_step`**, **`exists_cover_C`**, **`discEv_null`**, **`coupling_generic`**; `Forget/Halting.lean`: **`halting_branch_gen`**, **`halting_branch`** (D50, D51, F21: live drivers bounded by `𝓜` via Lemma 8.2, raw contours, `≤ 101f ≤ 512f` edges, `K_rare ε < 1`) | NEW | – | – | **DONE (s10)** |
| F5 **Lemma 8.5** (pullback and attraction) | **`pullbackEventuallySingleton_of_unique`**, **`forgets_of_unique`**, **`ergodic_of_unique`** (`PCA/Pullback.lean`, `PCA/Attraction.lean`), from "complete trajectories are a.s. unique (at time 0)" | NEW | – | – | **DONE (s2)**; the hypothesis is Lemma 8.4's conclusion |

### A.9 Effective constants and the main theorem (Section 9)

| node | planned Lean | kind | turns | risk | uses |
|---|---|---|---|---|---|
| Q1 (24), (26): `Δ = 10⁶(T+2)(9q+10)` (= 1480463260000000), `K_mem`, `K_hist`, `V`, `λ = 176`, `M = 196608`, `C = (128K_mem)^{-2}`; `Δ_rare`, `K_rare`, `N₀` | `UND.Param.Delta`, `Delta_eq`, `Kmem`, `Khist`, `V_eq`, `lam_eq`, `M_eq` DONE; `C`, `Krare`, `N0` | NEW | 2 | L | partly **DONE (s1)** |
| Q2 (25): the least `k ≥ 1` with `B = 4^k ≥ 20/C`, `4z_B < 1`, `η̂_B < min{…}`; existence (witness `k = 52386`) | `UND.Param.C`, `uB`, `zB`, `wB`, `etaHat`, `BSearch`, **`kParam := Nat.find`**, `exists_bsearch`, `bsearch_kParam` (`Parameters/Search.lean`) | NEW (Nat arithmetic by kernel on ~3·10⁵-bit numbers; no `2^{huge}` is built) | – | – | **DONE (s1)** |
| Q2' (the Scale paragraph) `k = 52386` exactly | **`kParam_eq`** (`bsearch_52386`, `not_bsearch_of_lt`; `⌊BC²/50⌋ = 322199` at `k = 52386`, `80549` at `52385`, as `scale_check.py`) | NEW | – | – | **DONE (s1)** |
| Q3 (27), (28): `ε_*`, the least `n₀ ≥ k + 2` (existence: the left side tends to `0`); (26) `N₀`, `Δ_rare`, `K_rare`; final windows | `DeltaRareOf`, `KrareOf`, `Krare`, `N0`, `Bparam`, `sParam`, `epsStarOf`, **`epsStar`**, `epsStar_pos`, `N0Search`, **`n0Param := Nat.find`**, `exists_n0Search`, `loF`, `hiF`, **`isWindowFamily_final`** (`Parameters/Threshold.lean`) | NEW | – | – | **DONE (s2)** |
| Q3' (optional) `n₀ = 888653587`, `log₁₀ ε_* = -535038537.39…` | – | NEW (bounds on `log N₀` to `±10⁻³`; never build `4^{n₀}`) | 8 | H | Q3 |
| Q4 **Lemma 9.1** (literal encoding bounds): doubled-edge traversal + source subset count `≤ Δ^{2e}2^{e+1}`; sums `≤ K_mem^g`, `≤ K_rare^g` (the history count `≤ K_hist^{f+m₀}W^{6c}` waits for Lemma 8.2) | `UND.Counting.finite_connected`, `card_enc_le`, **`card_encLe_le`**, `card_encLe_Kmem`, `card_encLe_KrareOf`, **`measure_le_tsum_groups`**, `measure_le_ofReal_tsum`; witness hook `connectedAt_image`, `connectedAt_filter_not_diag`, `pLen_le_two_pBin`, `witness_card_le`, **`witness_isEncoding`** (`Contour/Counting.lean`) | REUSE `FNE.EdgeCount.card_le_pow`, `exists_vertices` (D17) | – | – | **DONE (s3)** |
| Q5 **Prop 9.2** (parameter verification): noncircularity, termination, `I_n ⊂ (0, ε_*)`, `K_mem√C = 1/128`, `K_mem η̂_B^{1/6} < 1/64`, history and rare bases `< 1/64`, ruler margins (18) `ℓ_{a-1} < W`, `ℓ_a ≥ 2W` | interval clauses DONE (s2): **`window_subset`** (`I_n ⊂ (0, ε_*)`), `le_C_div_100`, `a_ge` (`a ≥ k + 3 ≥ 4`), **`ruler_margins`** (18). series bases DONE (s2, `Parameters/Bases.lean`): **`Kmem_sqrt_C`**, **`mem_eta_base_kParam`**, `mem_gamma_lt`, **`mem_series_lt`**, `raw_base_lt`, **`rare_base_lt_epsStarOf`**. History base DONE (s10, `Forget/HistBase.lean`): **`term_le`**, **`hist_base`**; single gates `ρ_B ≤ η̂_B < (64K_hist)^{-4}` and `K_rare ε < 1` (`Forget/Halting.lean`: **`gate_bounds_final`**, `eta_final`, `eps_hist_final`, `rare_final`) | NEW | – | – | **DONE (s10)** |
| Q6 windows (17): computable presentations, nonempty, in `(0,1)`, pairwise disjoint (`ℓ_{a+1} = 4ℓ_a + 3`) | **`UND.Windows.isWindowFamily_windows`** (every `c ≥ 1`, every `n₀`), `ell_succ`, `hi_lt_lo` | NEW | – | – | **DONE (s1)** `Windows.lean` |
| Q7 **Theorem 9.3** assembly | hook DONE (s3): `UND.Branches`, `window_rate`, **`noiseDiagram_of_branches`**, **`theoremA_of_branches`** (`Assembly.lean`); `theoremA_of_halting` (s9); final (s10): **`theorem_A := UND.Memory.theoremA_of_halting UND.Forget.halting_branch`** | NEW (D22, D52) | – | – | **DONE (s10)** |
| Q8 **Corollary 9.4** | `UND.corollary_9_4` | NEW | – | – | **DONE (s1)** from `theorem_A` |

### A.10 Hardest nodes

1. **Lemma 5.1** (C1): a genuine generalization of the forgetting core's contour lemma (groups,
   unequal times, unary links, inequality potentials); every probabilistic estimate of Sections 5,
   7, 8 depends on it. Start it early (it depends on nothing else). **DONE (s2)** in abstract
   form (`Contour/Grouped.lean`); what remains is building its instances (the graphs of Lemmas 5.2,
   5.4, 7.2, 8.4) and the counting of Lemma 9.1 on its witness.
2. **Lemma 3.3** (S8): the all-phase board argument within one closed frame (the item the second
   review flagged as missing in the draft, then repaired); UPD's routing analysis is for typical
   phases with unbounded walls and must be redone for a strip bounded by two walls.
3. **Lemma 4.1**(b) (M3): the halving/appending machine `P`; the hard-model core needed ~1500
   lines (`Label.lean`, `Ready.lean`, `Run.lean`) for its machine.
4. **Prop 4.3** (M5): **DONE (s6)** (`Chart/Construct.lean`, `Chart/ChartLaw.lean`; D32, D34).
5. **Lemma 5.3** (C3) and **Lemma 8.2** (F2): long deterministic/probabilistic arguments with
   delicate bookkeeping (provider-span induction; Hölder-mixed packing with compression).
6. **Lemma 6.3** (N4) and **Mem1**: independence on disjoint coordinate sets of
   `Measure.infinitePi`, and a measurable stationary helper initialization. **DONE (s8, s9).**

---

## Part B. Reuse inventory

### B.1 From the forgetting core (`FNE`, `/opt/forgetting-arxiv-2026-11-10/project`, read only)

Imported as prebuilt `.olean`s (`scripts/env.sh`). Statement level: `FNE.flagLaw`,
`FNE.WeakTendsto` (exact matches, used in `Statements.lean`). Proof level, REUSE as is:
`FNE.EdgeCount.card_le_pow` (`mem:count`: connected `n`-edge sets at a vertex `≤ Δ^{2n}`),
`FNE.EdgeCount.exists_covering_walk`, `ConnectedAt`, `Reach`; `FNE.isProbabilityMeasure_flagLaw`.
ADAPT (generic port, D3): `Section2/Process.lean`, `Markov.lean`, `Feller.lean`,
`ForgetErgodic.lean`, `Ergodic.lean` (A.1); `Combinatorics/Contour.lean` (Lemma 5.1);
`Section3/Peierls.lean` (Lemma 5.2 and every geometric-series union bound); the checker
definitions of `Statements.lean` (R1, R2).

### B.2 From the hard-model core (`UPD`, `/opt/undecidable-phase-diagram-arxiv-2026-11-11/project`, read only)

Statement level: `UPD.Machine`, `UPD.Machine.HaltsOn`, `UPD.Universal`, `UPD.ExistsUniversal`
(used in `Statements.lean`); proof level `UPD.Compiler.univMachine_universal` (used in
`Corollary.lean`). Scaffold, REUSE as is (Prop 3.1; names in A.3 S1): `UPD.Scaffold.desub`,
`tower_unique`, `exists_tower_of_tiling`, `TowerRel`, `IsInfTower`, `IsRank`, `dig`, `anc`,
`ancP`, `col`, `row`, `eq_digits`, `isRank_of_emod`, `rank_bits_col/row`, `red_col/row`,
`walls_col/row`, `walls_VW/HW`, `quarter_exists`, `quarter_unique`, `IsQPhase`, `qphase_local`,
`qphase_shift`, `exists_phase`, `ae_typical`, `Typical`, `quarter_ti_a`, `quarter_ti_law`,
`quarter_phase_haar`, `PhaseSystem`, `frameLo`, `frameHi`, `InFrame`, `IsFree`, `card_free`,
`frames_nested`, `frames_contain`, `endpoint_not_inFrame`, `Laminar`, `LegalOn`, `Letter.child`,
`se_spec`, `nw_spec`. The paper's Verification status names exactly these (`desub`,
`tower_unique`, `phase_local`, `red_col/red_row`, `rank_bits`, frames and laminar lemmas,
`quarter_exists/quarter_unique`); all audited strict in UPD (`propext`, `Classical.choice`,
`Quot.sound`). ADAPT: `UPD.BG.Line`/`EvLine` (routing along a line), `UPD.BG.cfg_legal`,
`wtag`, `evTag` (typical-phase routing existence = DMhard Props 5.1, 5.7, Lemma 5.3),
`UPD.MachineM` run lemmas (`Machine.lean`, `Run.lean`, `Label.lean`, `Ready.lean`).

### B.3 Not reused (and why)

* `FNE.run`, `FNE.law`, `FNE.IsInvariant`, `FNE.IsErgodic`, `FNE.IsPositiveRatePCA`: hard-wired to
  `quorumRule k R` on `Sym R` over `ℤ² × ℤᵏ`.
* `FNE.TuringMachine` (two-sided tape, blank input): the paper's `U` is one-way on unary inputs,
  which is `UPD.Machine`.
* `FNE.AuditCommand`/`UPD.AuditCommand`: both declare the same `#audit_axioms` syntax; ours is a
  copy under `UND.Audit` (with `#audit_prefix`), and neither of theirs is imported.

---

## Part C. Mathlib inventory and named hypotheses

* Mathlib (`56a0058`) has: `Measure.infinitePi` (product of probability measures), Tychonoff,
  `BoundedContinuousFunction`, `ComputablePred`, `Primrec`/`Computable` (with `Nat.Primrec.pow`;
  there is no `Primrec.nat_pow`, use `Primrec₂.unpaired'.1 Nat.Primrec.pow`), `PrimrecPred.decide`,
  the halting problem (`ComputablePred.halting_problem`), Chernoff via mgf
  (`ProbabilityTheory.measure_ge_le_exp_mul_mgf`), Hoeffding for sub-Gaussian sums
  (`ProbabilityTheory.measure_sum_ge_le_of_iIndepFun`, `Probability/Moments/SubGaussian.lean`),
  `Fin n` with discrete topology, `⊤` σ-algebra, `MeasurableSingletonClass` and (through
  `DiscreteMeasurableSpace`) `BorelSpace`.
* **Named hypotheses for the core: none planned.** The external results the paper uses are
  either in Mathlib (Chernoff 1952, Hoeffding 1963, Tychonoff), proved in the paper (Toom/Gács
  contours in the grouped form of Lemma 5.1; the Berman–Simon/Gács reference is credit, not an
  input), or ours and formalized (DMhard scaffold and routing in UPD, DMforget in FNE). Fallback,
  if the Mathlib forms do not fit Lemma 6.2: `H_Chernoff` (Chernoff 1952, the exponential-moment
  bound for sums of independent Bernoulli variables) and `H_Hoeffding` (Hoeffding 1963,
  Theorem 2), published by other authors, would enter as explicit named hypotheses in a
  `Hypotheses.lean`, listed in the scope statement. Our own results (DMhard Props 5.1, 5.7,
  Lemma 5.3; DMforget; DMst) may not enter as hypotheses.

---

## Part D. Design decisions (session 1; for QB)

* **D1 Statement of record.** `def TheoremA : Prop`, `def CorollaryNineFour : Prop` in
  `Statements.lean`; the theorems in `Main.lean` (QB's ruling for the forgetting core, session 9,
  and the hard-model core: the proof needs every file, which imports the statement file). The
  brief asked for `theorem … := by sorry` targets in `Statements.lean`; they are in `Main.lean`
  instead, for this reason (`UND.theorem_A … := by sorry`). The statement file needs no edit when
  the proof lands.
* **D2 Reuse by import of prebuilt oleans, no lake.** `LEAN_PATH` = our build tree, the two cores'
  build trees and the pinned vendor tree (`scripts/env.sh`); builds by `scripts/build.py` with
  `lean -j1 -M5000` per module. Lake path packages are not used here because lake would write
  trace files into the two read-only `/opt` projects (and the earlier relays also build through a
  replay script). Release plan (Part F): `cp -a` both cores (sources + `.lake/build`) under
  `vendor/` of the release workspace as path packages, as the relays did for Mathlib.
* **D3 Generic PCA layer.** One generic port of the forgetting core's Section 2 (process,
  Markov, Feller, forgetting ⇒ ergodic, memory ⇒ non-ergodic) to `CA d`, then used by Thm 7.3 and
  Lemma 8.5.
* **D4 Chart alphabet as a finite type with matching relations** (UPD's `LegalOn`), not as
  ℕ-coloured FNE tiles; the paper's "recode as a Wang set by overlapping blocks" is then a
  definitional higher-block construction.
* **D5 Coordinates.** `Site 6 = Fin 6 → ℤ`; internally `ℤ² × ℤ⁴` by an explicit equivalence.
* **D6 Alphabet.** `Σ = 𝒜_R × 𝒜_R × (Fin B → ℋ)` as a Lean type; the CA alphabet is
  `Fin (Fintype.card Σ)`; the uniform law is transported (R6).
* **D7 Lane-phase decoder from `qphase_local`** (proof side): the paper's terminating search for a
  central radius is replaced by the explicit radius `ρ_l = 2^{l+1} - 2` of UPD's `qphase_local`
  (the residue `τ mod 2^l` is determined by the quarter tiling on `[-ρ_l, ρ_l]²`). Same table.
* **D8 Searches.** `k` and `n₀` are `Nat.find` of the printed predicates (least, as printed). The
  exact values `k = 52386`, `n₀ = 888653587` belong to the Scale paragraph (optional leaves Q2',
  Q3'); the theorem never evaluates `4^{n₀}` or `N₀`.
* **D9 Windows.** Proved for every `n₀` and every `C = 1/c`, `c ≥ 1` (`isWindowFamily_windows`), so
  the statement-level interval clauses do not wait for the searches.
* **D10 Pullback clause** rendered per finite window, almost surely, with eventual agreement of all
  starts (`PullbackEventuallySingleton`).
* **D11 "Computably specified".** For a fixed machine `U`, the automaton is one finite object; the
  adjective has no formal content and is not rendered (fidelity item F9 in `STATUS.md`). Optional
  strengthening for QB: `∃ A : UPD.Machine → CA 6, Computable-presentation(A) ∧ …` (uniform in `U`,
  as in the forgetting core's `Computable familyR`), which would cost an encoding of `CA 6` and a
  `Computable` proof of the whole construction (est. +15 turns, the forgetting core's session 9).

---

## Part E. Order of work (sessions 2 onward)

1. Session 2 (DONE): A.1 P4–P9 (the whole PCA layer), Q3, the interval clauses of Q5, C1
   (Lemma 5.1, abstract form), F5 (Lemma 8.5 from uniqueness of complete trajectories).
   Also the series bases of Q5 (all but the history base).
2. Session 3 (DONE): Q4 (Lemma 9.1, union bound over literal encodings, witness hook); A.2 R1–R6
   and Prop 2.1 generic in the chart tile set; the assembly hook Q7 (`theoremA_of_branches`); A.3 S1
   wiring (walls in every phase), the arithmetic of S5 (FD2) and S6.
3. Session 4 (DONE): A.3 S3–S8 (decorated alphabet and Lemma 3.2, lane-phase decoder, `Orig`/`End`,
   routing alphabet `R` with its `ChartData`, `theCA`, Lemma 3.3 as building blocks), M1 (machine
   `P`), the D17 variant `pLen_le_three_pBin`.
4. Session 5 (DONE): M2–M4 (Lemma 4.1, Lemma 4.2), indexed Lemma 3.3, M6 (Prop 4.3 halting).
   Session 6 (DONE): M5 (Prop 4.3 nonhalting: the chart of a typical phase and the TI chart law;
   D31's measurability of `Typical`), C3 (Lemma 5.3, also for the complete trajectories of the
   automaton).
5. Session 7 (DONE): C2, C4 (Lemmas 5.2, 5.4: the `GroupedSystem` instances on the marked
   derivation and on the virtual levels of a deep query, with Lemma 9.1's counting).
6. Session 8 (DONE): N1–N4 (Section 6 complete), the Lemma 7.2 combinatorial core and the helper
   ride of Lemma 7.1. Session 9 (DONE): Section 7 (Mem1, Mem2 derivation, Mem3 instance, Mem4:
   Theorem 7.3; `theoremA_of_halting` reduces Theorem A to the halting branch).
7. Session 10 (DONE): Section 8 (F1, F2, F4; F3 not needed), the history base of Prop 9.2, the
   assembly (`theorem_A := theoremA_of_halting halting_branch`), census 0, strict audit, lint.
8. Next sessions: release package (Part F).

---

## Part F. Estimate

Remaining after session 10: **0** for the core (census 0); 1–2 sessions of release packaging.
(Session 10 closed the estimated ≈ 37 turns of Section 8, the history base and the assembly in one
session: F21 replaced Lemma 8.3 and the birth contours by the raw contours of Lemma 5.2.)
(Session 9 closed ≈ 24 estimated turns: Mem1 8, Mem2 5, Mem3 4, Mem4 6, F1 first step 1; Section 7
complete.)
(Session 8 closed ≈ 24 estimated turns: N1 1, N2 4, N3 2, N4 8, Mem3 core 6, Mem2 ride 3.)
(Session 7 closed ≈ 27 estimated turns: C2 (8), C4 (6), N3's core (8), N1's laws (5).
Session 6 closed ≈ 29: M5 (17) and C3 (12).)
(Session 4 closed ≈ 42 estimated turns: S3–S8 and M1. Session 5 closed ≈ 30: M2, M3, M4, M6 and
the indexed Lemma 3.3; M5's estimate was raised from 12 to 20 after reading the hard-model core's
`Construct.lean` and `BgMap.lean`.)
Done after session 3: everything of sessions 1–2 (statement, corollary reduction, windows,
constants, `k = 52386`, black-type comparison, abstract cutoff lemma, the PCA layer P1–P9, `ε_*`
and `n₀`, the interval clauses and series bases of Prop 9.2, Lemma 5.1, Lemma 8.5) and, in
session 3, Lemma 9.1, the whole rule of Section 2 with Prop 2.1 (generic in `R`), the Theorem 9.3
reduction to its two branches, and the first A.3 pieces (about 27% of the total). Session 4: all of
A.3 (Lemma 3.2, the lane-phase decoder, `Orig`/`End` and the gates, the routing alphabet `R`, the
automaton `theCA U` with Prop 2.1 for it, Lemma 3.3 in every phase) and M1 (about 41% of the total
done).

Release package (after census 0): `Challenge.lean` (Mathlib only) with transparent copies of
`FixedNoiseErgodicity/Statements.lean` (with `setMainModule`), `UndecidablePhaseDiagram/Statements.lean`
(compiled with `backward.isDefEq.respectTransparency=false`, as in the hard-model challenge) and
our `Statements.lean`, then the holes `UND.theorem_A : UND.TheoremA` and
`UND.corollary_9_4 : UND.CorollaryNineFour`; `Solution.lean` imports `UncomputableNoiseDiagram.Main`;
`comparator.json` permits `propext`, `Classical.choice`, `Quot.sound`; leanchecker and nanoda
replays of the Solution export; read by eye against `main.pdf`.

---

## Part H. Corollary B (`ℤ⁷` Gibbs), not in the core

How it would enter: define the space–time interaction `Φ_{w,t}(σ) = 1{σ(w,t) ≠ f(σ(w + N_F, t-1))}`
on `ℤ⁶ × ℤ`, its Gibbs specification (reuse `UPD.Interaction`, `UPD.IsGibbs`, generalized from
`ℤ²` to `ℤ⁷`: the hard-model definitions are planar), the map `ε(β) = N_Σ/(e^β + N_Σ - 1)` and the
normalization identity (elementary), and the window transport `𝒥_n` (rational approximation of
computable reals). The correspondence between spatially translation-invariant stationary laws of a
positive-rate finite-range PCA and space–time-translation-invariant Gibbs measures enters as a
**named hypothesis `H_GKLM`** (Goldstein, Kuik, Lebowitz and Maes, Comm. Math. Phys. 125 (1989)
71–79, doi:10.1007/BF01217769), stated for finite alphabets, finite range, positive rates, every
spatial dimension. The paper invokes it "in the form proved in our space–time paper" (DMst Lemma
2.4, Cor 10.4): since DMst is ours, the hypothesis must be phrased as the published GKLM statement,
not as DMst's lemma. The extra clause "the only uniformly recurrent, hence the only periodic, Gibbs
measure" uses DMst Theorem 10.10(i), ours and not formalized: it would need a Lean proof or be
dropped from a formal Corollary B. Estimate: 10–15 turns plus the hypothesis sign-off.
