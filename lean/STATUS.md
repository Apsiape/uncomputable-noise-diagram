# Status (session 11, 11 Nov 2026)

**Session 11: the release package.**
* **Where.** The package was built in the new WSL workspace `/opt/uncomputable-noise-diagram-arxiv-2026-11-12`,
  from `git archive ec67163`. The two cores are vendored as sources and compiled there. No `LEAN_PATH`
  shortcut was used.
* **Results.** Build from a clean copy: PASS (117 modules, `-j1 -M5000`). Sandboxed
  `lake comparator`: PASS (targets `UND.theorem_A`, `UND.corollary_9_4`, `UND.one_rule_undecidable`).
  Kernel replays of the Solution export: leanchecker PASS, nanoda PASS, with the negative control
  rejected. Fresh axiom audit: PASS. It covers 3,712 development declarations and 4,452 imported core
  declarations, and only the three standard axioms occur.
* **Records.** The statement eye-read (`STATEMENT-READ.md`) finds `Statements.lean` faithful. The scope
  is in `SCOPE.md`. The evidence is in `evidence/` and `relay/`.
* **The challenge.** It uses one new auxiliary command for QB: emptying Lean's per-file
  auxiliary-proof cache before each copy (`relay/make_challenge.py`).
* **Not yet committed.** The relay report `REPORT.md` was drafted but could not be written by the
  session 11 agent.

Lean core of S. Douglas and N. Mghirbi, "One noisy cellular automaton with an uncomputable noise
diagram", v1.1.0 (Zenodo DOI 10.5281/zenodo.24152233; v1.0.0 was 10.5281/zenodo.24147269; Theorem A,
Theorem 9.3 and Corollary 9.4 are byte-identical in both). Core: Theorem 9.3 (Theorem A) and
Corollary 9.4. Pin: Lean v4.35.0 (`eb6cafb7…`), Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`.

**Session 10: the core is complete.** Sorry census **0**; `UND.theorem_A`, `UND.corollary_9_4` and
`UND.one_rule_undecidable` depend only on `propext`, `Classical.choice`, `Quot.sound` (`AXIOMS.txt`,
AUDIT OK, 3615 declarations, none depending on `sorryAx`).

## Rulings (QB, session 10)

* **Source version.** Version 1.1.0 of the paper is RELEASED (DOI 10.5281/zenodo.24152233; text:
  `C:/Infanox/uncomputable-noise-diagram-release/paper/main.tex`). QB verified that Theorem A (the
  introduction's statement), Theorem 9.3 and Corollary 9.4 are byte-identical to v1.0.0.
* From session 10 on, every remaining intermediate statement and proof (Section 8, Prop 9.2's
  history base) is read from v1.1.0, the corrected text; in particular v1.1.0's Lemma 8.4
  birth-contour clock convention (its correction (iv)). **Applied (s10):** Section 8 and the history
  base were read from v1.1.0. The route taken for Lemma 8.4 builds no birth contours (F21), so the
  clock convention of correction (iv) is not exercised; nothing in the formalization conflicts with
  it.
* v1.1.0 also corrects Lemma 5.1 (FD1), §3.2 (FD2) and Prop 2.1's count, so those fidelity
  deviations now MATCH the released text. **Applied (s10):** the FD entries are kept as history
  ("printed in v1.0.0; corrected in v1.1.0") and the fidelity table states that the formal targets
  match v1.1.0.
* v1.1.0 sharpens Theorem 7.3's internal bound (`e_base < 3/125`). The already-proved Theorem 7.3
  with the v1.0.0 bound (`S < 1/4`) remains a valid proof of the same statement; **not redone**.
* The new v1.1.0 results (Theorems 9.5–9.7, Corollary B's all-Gibbs upgrade, Theorem B.1) are NOT
  in the core.
* Standing: the construction's printed parameters (unchanged in v1.1.0) are kept; Theorem A's
  statement never changes (`Statements.lean` is unchanged since session 1); the generic-bridging
  pattern of session 9 is followed (the halting branch is proved generically in `CD`, `B` and for
  `theCAOf U n₀ k s` with variable parameters, then instantiated once).

## Rulings (QB, session 9)

* **D41: CONFIRMED.** Keeping every link inside each group and counting them linearly (at most
  `25g`: a group receives at most one arm end per charge) resolves D14(b), provided the encodings
  feed exactly the printed union bounds: at most `256g` edges and `K_mem` for Lemma 7.2, at most
  `512g` and `K_rare` for Lemma 8.4. Recorded as a proof-route difference (F19). **D14(b) is
  closed.** Lemma 7.2 as instantiated (s9, `Memory/Derivation.lean`, `Memory/Error.lean`) feeds
  `mem_encoding` (`≤ 256g` edges) into `mem_union` (`K_mem`), exactly the printed bound; Lemma 8.4
  must feed `≤ 512g` edges into `K_rare` (`card_encLe_KrareOf`).
* **D40: CONFIRMED.** Per bin at most `4^r` short ends and one long end (an intermediate
  strengthening, F18); `S(χ, i)` is "some finite phase-zero gate ending in the bin has its bad event
  (short below depth `a`, long from `a` on)"; the Cauchy–Schwarz step is
  `P(X ∩ Y) ≤ √(P X · P Y)`.
* **D42: CONFIRMED, with one required check.** The stationary helper initialization is rendered on
  the two-sided noise (`HelperTraj`): data and the second coordinate are held at the chart for
  `t ≤ 0`, helpers follow rule (4) with the chart's drivers. The resulting time-0 initial law, built
  from the chart law, must be translation invariant and must be the initial law of the paper's
  Section 7 (Theorem A's "two translation-invariant stationary laws" comes from Cesàro limits of TI
  initial laws, `hasTwoTIStationaryLaws_of_memory`); prove that invariance explicitly, as part of
  Mem1. **Done (s9):** the initial law is `memLaw t0 b ε = initLaw sParam haar (cSf t0 b) ε`
  (`Memory/Theorem.lean`): the push-forward of Haar phase ⊗ negative-time noise along `X0`, the
  time-0 state of the hybrid trajectory `hyb` (data and second coordinate the bit-`b` lift of
  `chartOf τ`, helpers the ideal chart-driven fields). Its translation invariance is proved
  explicitly: **`memLaw_TI`** (from **`initLaw_TI`**, `X0_shift`, `cSf_shift` (=`chartOf_shift`),
  `haar_map_addDig`, `noiseLaw_map_shiftNoise`), and Theorem 7.3 takes Cesàro limits of exactly
  these laws (`memory_branch` → `hasTwoTIStationaryLaws_of_memory`, `theorem_7_3`).

## Rulings (QB, session 8)

* **D35: CONFIRMED.** An ordinary dependency step is `(u, P, t) → (u + μ, P + s, t - 1)`, `μ` a
  Moore displacement and `s` a provider offset; centre parents are the case `μ = 0`. Proving
  Lemma 5.2 under `K_mem ε < 1` (weaker than printed) is fine: intermediate lemmas may be stronger
  than printed when they imply the printed uses. Recorded as an intermediate strengthening (F18).
* **D36: CONFIRMED.** "Relative to the chart in Lemma 5.3" is the hypothesis that the chart agrees
  with every unmarked live reading (what `coherent_chart` supplies). `f ≥ 12`, `e ≤ 48(f-1)` are
  stronger than the printed `f ≥ 11`, `e ≤ 50(f-1)`: recorded as an intermediate strengthening
  (F18). QB: make sure the downstream uses (Lemma 6.3, Section 8) consume the form proved. Note
  (s8): Lemma 6.3 does not use Lemma 5.4 (its formal statement `joint_source_bound` has no deep
  query); the consumer is Lemma 8.2 (Section 8), which must take `deep_wrong`/`deep_wrong_lag` as
  proved (`f ≥ 12 ≥ 11`, `e ≤ 48(f-1) ≤ 50(f-1)`); noted in `HANDOFF.md`.
* **D37/D38: CONFIRMED.** Tails for abstract independent indicators; the per-gate sites and counts
  come with Lemma 6.1, and (14)/(15) apply along a given list of distinct noise sites. **Done
  (s8):** `Sensors/Ownership.lean`, `Gate.lean`, `Joint.lean`, `Selected.lean`.
* **D14(b):** still flagged for Lemma 8.4. (Session 8 proposes a resolution, D41: a linear count
  of group links replaces the star sub-witness; for QB.)
* **Risk 7 (host memory guard):** waiting was correct; never bypass the guard; if it refuses for
  long, commit what builds and continue with non-build work. (No refusal in session 8.)

## Rulings (QB, session 7)

* **D32: CONFIRMED.** Building the translation-invariant chart law as the Haar pushforward of
  `τ ↦ chartOf τ` is a different proof route to the printed conclusion. The core is held to its
  STATEMENTS as printed, not to the printed proof route. Recorded in the fidelity table as a
  proof-route difference (F17).
* **D33: CONFIRMED.** Lemma 5.3 for every flagged trajectory and every marked set closed under the
  two marking rules covers the paper's raw marked set and its `t₀ → -∞` limit. Working on the limit
  `𝓜` directly is fine.
* **D34: noted.** The chart's routing fields are the hard-model core's construction unchanged
  (DMhard Props 5.1, 5.7, Lemma 5.3). Kept here for the release scope table: *the routing tags of
  the chart of a typical phase (`rawVal`, `Chart/Construct.lean`) are `UPD.BG.cfg` verbatim, with
  (O1)–(E3), activity and carriers from the hard-model core's proved lemmas.*
* **D14(b):** still flagged for Lemma 8.4.

## Rulings (QB, session 6)

* **D29: CONFIRMED.** Lemma 4.1(b)'s clause "any other positive count eventually fails" may stay
  unformalized: Prop 4.3 never uses it (Lemma 4.2 forces `j_* + 2 = 2^{a+1}`). The arXiv bar is
  Theorem A and Corollary 9.4 as printed, not every intermediate clause. Recorded in the fidelity
  table as F16, "printed intermediate clause not formalized (unused)".
* **D31: CONFIRMED, on one condition.** Section 7's "almost every phase" may be taken over the
  hard-model core's `Typical` (resolving, both coordinates non-integer, `Digit2`), since the routing
  existence needs it. Condition: the development must prove (or import as a proved declaration)
  that `Typical` is measurable and has full Haar measure, in the form Section 7's phase averaging
  needs. **Done (s6):** the hard-model core proves only `ae_typical` (`∀ᵐ τ ∂haar, Typical τ`);
  measurability is new here: `UND.Chart.measurableSet_typical` and `UND.Chart.haar_typical`
  (`haar {τ | Typical τ} = 1`), `Chart/ChartLaw.lean`, strict audit; blueprint node M5.
* **D30:** noted.
* **D14(b):** still flagged for Lemma 8.4.

## Rulings (QB, session 5)

* **D28: ACCEPTED** as fidelity choices for machine `P`'s prose (each is noted in the fidelity
  table, F15 below): `RET_Z` is a stay move; a halting `q` enters HALT with a stay move; a halting
  successor moves as `U` does, so a move off cell `0` fails (matching `UPD.Machine.step = none`); a
  failing head at a tape end keeps the written symbol.
* **D26: ACCEPTED.** "Typical chart" means phase coordinates that are not integers (`NotInt`). This
  is a full-measure (Haar-typical) set, as in the hard-model core. When Prop 4.3 and Section 7 use
  typicality, check that this notion is exactly what they need, and that the memory branch's
  "almost every phase" statements are taken over this set.
* **D24: ACCEPTED.** `B = 4^kParam` literally, with no closed equation (D13).
* **D14(b): still flagged** for Lemma 8.4.
* Standing: keep v1.0.0's printed parameters; formalize the correct statement where the printed
  text is wrong and log an FD; Theorem A's statement never changes. v1.1.0 (in preparation) repairs
  Lemma 5.1's span clause (FD1), §3.2 (FD2) and the Prop 2.1 count.

## Rulings (QB, session 4)

* **FD2: CONFIRMED.** The printed line "the phase-zero gates are exactly the finite bottom rows with
  `d ≥ k`" is false read globally (a cross-family check found exceptional infinite-rank phase
  limits) and correct restricted to gates on finite bottom rows. `lanePhase_bot_eq_zero_iff` (on a
  finite bottom row of depth `d`: phase `0 ⟺ d ≥ k`) is the intended correction; the tile-level
  forms are `end_gate` (quarters) and `IsRChart.gate_iff` (tiles of `R`), session 4.
* **Prop 2.1 count: ACCEPTED.** The formal neighbourhood has `B` helper sites (the printed `B + 1`
  counts `w - e_x + v` twice) and the printed bound `κ` holds. Recorded as a printed miscount, not a
  deviation of any statement; QB passes it to the v1.1.0 text check.
* **D17: fidelity first.** Read Lemma 7.2 as printed. **Outcome (session 4):** the printed proof
  does *not* merge the corridor: "Suppress each maximal source-free characteristic corridor to a
  corridor link and its entry link … at most two unary entry/corridor links per positive support
  edge, plus at most `5g` terminal source-role links. The total is less than `149g < 256g`." So the
  second branch of the ruling applies: the variant **`pLen_le_three_pBin`** (with
  `gLen_le_three_gBin`; hypothesis: no unary link is followed by two more) is added to
  `Contour/Counting.lean` and is the one Lemma 7.2 will use (`3·48(g-1) + 5g < 149g`, the printed
  count). `pLen_le_two_pBin` (merged form) stays as a lemma but is not the instance.
* **D14(b): still flagged.** Lemma 8.4 counts a star sub-witness (at most `5g` group links).
* **D21: ACCEPTED as the standing pattern.** `T = 500`, the iterations of `F_R` and the concrete
  neighbourhood sets stay locally irreducible.
* Standing: keep v1.0.0's printed parameters; where printed text is wrong, formalize the correct
  statement and log an FD; Theorem A's statement never changes.

## Rulings (QB, session 3)

* **D13 (kernel blow-up): ACCEPTED** as the standing pattern: constants derived from `kParam`, `B`,
  `N₀`, `K_rare` stay functions of their parameters with lemmas over variables; closed constants
  enter only through one-step instances.
* **D14(b) (witness group links / star sub-witness): ACCEPTED**; star counting is left to
  Lemma 8.4 and stays flagged here (see D14 below and the open risks).
* **D15 (Lemma 8.5 hypothesis as "a.s. any two complete trajectories agree at time 0"): ACCEPTED.**
* **Parameters:** formalize with v1.0.0's printed parameters (`w_B = 2^{-⌊BC²/50⌋}`,
  `k = 52386`, …); a later v1.1.0 may use a sharper Chernoff tail; Theorem A does not change. Do
  not switch.
* **Fidelity rule:** where v1.0.0's printed text is wrong, formalize the correct statement and log
  an FD entry. Known: FD1 (Lemma 5.1's span clause, done in session 2) and FD2 (§3.2's finite-gate
  classification, restricted to gates on finite bottom rows; done in session 3).

## Rulings (QB, session 2)

* **D1: CONFIRMED.** `def TheoremA : Prop` stays in `Statements.lean`; the theorem targets stay in
  `Main.lean`, as in the forgetting core.
* **F9: ACCEPTED.** "Computably specified" is not rendered; the fidelity note (F9 below) explains
  why. The computable family `U ↦ A_U` is **not** to be added: `TheoremA` is stated for every
  machine `U`, which is stronger.
* **Statement choices: all ACCEPTED** — rates with `0 < lo` and `hi < 1` (F10); endpoints by
  computable presentations as pairs of naturals (F10); every machine `U` (F12); the pullback clause
  as written (F8); Corollary 9.4 as a promise problem (F13). QB read `Statements.lean` against
  Theorem 9.3 and Corollary 9.4 and finds it faithful.
* **Kernel limit:** keep generalizing huge closed exponents to variables before any proof touches
  them (session 2 extends this to every huge closed constant, see D13 below).
* **Release plan:** `cp -a` both cores under `vendor/`, and verbatim statement files in the
  Challenge: ACCEPTED for the end, not now.

## What builds

Full serial capped build in WSL (`scripts/wsl.ps1 audit`: `lean -j1 -M5000`, one process at a
time, ≥ 8 GiB available checked before each module; the Windows host is checked too): **OK**,
74 modules (session 10), every module under 30 s.

| module | content | status |
|---|---|---|
| `UncomputableNoiseDiagram/Statements.lean` | statement of record (unchanged since session 1) | builds, no proofs of substance |
| `UncomputableNoiseDiagram/Main.lean` | **`UND.theorem_A := UND.Memory.theoremA_of_halting UND.Forget.halting_branch`** (closed, s10), `UND.corollary_9_4`, `UND.one_rule_undecidable` | **DONE (s10)**, strict |
| `UncomputableNoiseDiagram/Corollary.lean` | Cor 9.4 from Thm 9.3; one-rule corollary | DONE (s1), strict |
| `UncomputableNoiseDiagram/Windows.lean` | the intervals (17): a computable disjoint window family (every `n₀`, every `C = 1/c`) | DONE (s1), strict |
| `UncomputableNoiseDiagram/Parameters/Geometry.lean` | (1), (11), (13), Section 8 and Lemma 9.1 constants, Prop 2.1 arithmetic | DONE (s1), strict |
| `UncomputableNoiseDiagram/Parameters/Search.lean` | the search (25): `kParam := Nat.find`, `kParam_eq : kParam = 52386` | DONE (s1), strict |
| `UncomputableNoiseDiagram/Parameters/Threshold.lean` | Q3: (26) as functions of `B` (`DeltaRareOf`, `KrareOf`), `N0`, `Bparam`, `sParam`; `ε_*` (27) (`epsStarOf`, `epsStar`, positivity and the four bounds); the search (28) `n0Param := Nat.find` with existence; the final windows `loF`, `hiF` (`isWindowFamily_final`); Prop 9.2 interval clauses: `I_n ⊂ (0, ε_*)`, `ε ≤ C/100`, `a ≥ k + 3 ≥ 4`, ruler margins (18) | **DONE (s2)**, strict |
| `UncomputableNoiseDiagram/Parameters/Bases.lean` | Q5, the series bases of Prop 9.2: `K_mem √C = 1/128`, `K_mem η̂_B^{1/6} < 1/64` (abstract `B` and the selected one), `K_mem γ < 3/128`, `Σ_{g≥1}(K_mem γ)^g < 1/4`, raw-path base `K_mem ε < 1/64`, rare base `K_rare(N₀ε^M)^{1/16} < 1/64` (abstract `B`, `N₀`) | **DONE (s2)**, strict |
| `UncomputableNoiseDiagram/Chart/BlackType.lean` | black-type rank comparison; abstract Lemma 3.2 (first sentence) | DONE (s1), strict |
| `UncomputableNoiseDiagram/PCA/Process.lean`, `Markov.lean` | P1–P3: noise laws, locality, measurability, `law`, one-step product form, Markov property, positive rates | DONE (s1), strict |
| `UncomputableNoiseDiagram/PCA/Cylinder.lean` | cylinders and their indicators, `HasMemoryFrom` (two initial laws), `not_ergodic_of_memoryFrom`, `dtv`, `deltaO`, `Forgets`; NEW coupling bound `dtv_law_dirac_le`, `forgets_of_coupling` | **DONE (s2)**, strict |
| `UncomputableNoiseDiagram/PCA/Feller.lean` | P4: continuity of `F` and of the process, `Phi`, Feller property, Cesàro averages, `isStationary_of_cesaro_limit`, `exists_cesaro_limit`, `exists_stationary`, `weakTendsto_iff_cyl`, `weakTendsto_iff_dtv` | **DONE (s2)**, strict |
| `UncomputableNoiseDiagram/PCA/Translation.lean` | P5: `apply_shift`, `run_shift`, translation invariance of the noise law, `law_map_shift`, TI laws, TI Cesàro averages, TI weak limits, `isTI_of_cesaro_limit` | **DONE (s2)**, strict |
| `UncomputableNoiseDiagram/PCA/ForgetErgodic.lean` | P6–P7: `ergodic_of_forgets`, `two_stationary_of_memory`, `hasTwoTIStationaryLaws_of_memory` (Thm 7.3, last paragraph), `not_ergodic_of_two`, `noiseDiagram_clauses` | **DONE (s2)**, strict |
| `UncomputableNoiseDiagram/PCA/Pullback.lean` | P9, Lemma 8.5 first assertion: `IsComplete`, nested pullback images, `exists_complete_of_pullback` (product compactness), `pullback_eventually_singleton_of_unique`, `pullbackEventuallySingleton_of_unique` | **DONE (s2)**, strict |
| `UncomputableNoiseDiagram/PCA/Attraction.lean` | P8, Lemma 8.5 second assertion: dependence cone, measurable coupling-failure events, time homogeneity of the two-sided noise (`noiseLaw₂_map_tau`, `noiseLaw₂_pullFail`), `forgets_of_unique`, `ergodic_of_unique` | **DONE (s2)**, strict |
| `UncomputableNoiseDiagram/Contour/Grouped.lean` | C1, **Lemma 5.1** abstract form: `GroupedSystem`, greedy arms, poles, fronts and the splitting invariant on group names, `exists_bij`, `grouped_terminal_estimate`, `grouped_terminal_estimate_paper` (12), the copied-arm `witness` and `witness_connected`, `singleton_two_le`, `witness_span` | **DONE (s2)**, strict |
| `UncomputableNoiseDiagram/Contour/Counting.lean` | Q4, **Lemma 9.1**: connected `n`-edge sets in a graph of degree `≤ Δ` (`finite_connected`, generic port of FNE's), literal encodings `(K, A)` (edges + marked source subset), `card_enc_le` (`Δ^{2n}2^{n+1}`), **`card_encLe_le`** (`≤ 4(2Δ²)^N`), `card_encLe_Kmem` (`≤ K_mem^g`, `N = 256g`), `card_encLe_KrareOf` (`≤ K_rare^g`, `N = 512g`), the union bound **`measure_le_tsum_groups`** (`μ(Ev) ≤ Σ_{g≥1}(Kx)^g`) and its real form; hook to Lemma 5.1: `connectedAt_image`, `connectedAt_filter_not_diag` (projection, collapsed links), `pLen_le_two_pBin`, `witness_card_le`, `grpEdges_card_le`, **`witness_isEncoding`** | **DONE (s3)**, strict |
| `UncomputableNoiseDiagram/Rule/Checker.lean` | R1, R2: `WangRel` (D4), legal blocks, live letters, `ChartSym = Option`, `Compatible`, `IsFullChart`, `Keeps`, `chk`; providers `Prov` (`|Prov| = q`, coordinates in `[0,175]`); **`FR`** (`F_R`), **`quorum_unique`** (`2h > q`), `FR_eq_some_iff`, `FR_eq_none_iff`, **`FR_cloned`**; `FR_translate`, `FR_local`, `FR_iter_translate`, **`FR_iter_local`** (locality of `F_R^n` on `[-n,n]² × [0,175n]⁴`) | **DONE (s3)**, strict |
| `UncomputableNoiseDiagram/Rule/Proposal.lean` | R3, R4: `Ival`, `Helper = Fin 100` (`rep`, `repr`, counts 1/1/98), `ChartData B τ`, `PhysSym` (2), `drvA`, `drvQ` (3), `Jf` (4), `hcount`, `lcount`, `Pin` (5), **`proposal`** (6); **`proposal_translate`**, **`proposal_local`** (`B ≥ 1`) on `nbhdP B`, **`card_nbhdP_le`** (`≤ B(n_A+n_Q)+B ≤ B(n_A+n_Q+2)`) | **DONE (s3)**, strict |
| `UncomputableNoiseDiagram/Rule/CA.lean` | R5: `siteEquiv : ℤ⁶ ≃+ ℤ² × ℤ⁴`; `caOf G N` (a local translation-commuting map is a `CA 6`), **`caOf_apply`**; `ruleCA CD s`, `ruleCA_apply`, **`prop_2_1`** (global map = (6), `2|N_F| ≤ κ`) | **DONE (s3)**, strict |
| `UncomputableNoiseDiagram/Rule/Noise.lean` | R6: `update_decode` (a noisy update read in `Σ` and `ℤ² × ℤ⁴`), `uniformLaw_decode` (`P(Z ∈ E) = |E|/|Σ|`), **`uniformLaw_field`** (each helper field of the replacement mark is uniform on `ℋ`) | **DONE (s3)**, strict |
| `UncomputableNoiseDiagram/Chart/LanePhase.lean` | S5 arithmetic: `lanePhase` (9), `lanePhase_succ`, **`lanePhase_bot`** (`p(Bot_d) ≡ (4m+1)4^d mod 4^{min(d+1,k)}`), **`lanePhase_bot_eq_zero_iff`** (FD2: on a finite bottom row of depth `d`, `p = 0 ⟺ d ≥ k`) | **DONE (s3)**, strict |
| `UncomputableNoiseDiagram/Chart/Walls.lean` | S1 wiring: **`walls_VW_of_rank`**, **`walls_HW_of_rank`** (light walls at a coordinate of finite parent rank, in every phase; UPD's `walls_VW/HW` without `NotInt`); S6: `frameHi_sub_frameLo` (`R_d - L_d = ℓ_d`) | **DONE (s3)**, strict |
| `UncomputableNoiseDiagram/Chart/Origins.lean` | S6, S8 first step: `PRank` (parent rank of a physical coordinate), **`exists_prank_le_of_inFrame`** (Lemma 3.3 first step: closed-frame coordinates have finite parent rank `≤ 2d`, every phase), `IsOrig`, `IsEnd`, **`bottom_corner_iff`**, **`orig_iff`**, **`end_iff`** (one finite rank suffices), **`end_gate`** (FD2 at an `End` on a finite bottom row) | **DONE (s4)**, strict |
| `UncomputableNoiseDiagram/Chart/Decorated.lean` | S3, S4: `rankOK` (filter (8)), `DTriple`, `DLetter`, `DQuarter` with Wang colours (`colE … colS`), `matchE_iff`, `matchN_iff`, `toQ`, `isQTiling_toQ`, `H_row_const`, `V_col_const`, **`cutoff_of_dtiling`** (Lemma 3.2 first sentence, every phase), **`cutoff_exists`** (every finite cutoff over every chart with non-integer phase coordinates) | **DONE (s4)**, strict |
| `UncomputableNoiseDiagram/Chart/PhaseTable.lean` | S5 decoder (D7, D25): `winRad k = ρ_{2k}`, `Word`, `wordAt`, `Liftable`, `phaseTable`, `exists_qphase_shift`, **`phaseTable_wordAt`** (the table reads (9) on every tiling, every phase), `…_eq_lanePhase`, `…_eq_zero_iff`, `…_add_e1`, `…_add_e2` | **DONE (s4)**, strict |
| `UncomputableNoiseDiagram/Machine/P.lean` | M1: `Tape`, `Cont`, `PState U n0`, `program` (clauses 1–6), `deltaP`, `Cell` (`S_P`), `fromBelow`, `fromAbove`, **`fP`** (ordered rule), `initP`, `CarriesHalt` (definitions only) | **DONE (s4)** (defs) |
| `UncomputableNoiseDiagram/Chart/Routing.lean` | S7 (D24, D26): `ContentOps`, `RVal` (tuple), `O1 … E3`, `K1`, `K2`, `C0`, `Tab` (10), `K3`, `Allowed`, colours; `TileOK`, **`RTile`** (the alphabet `R`), `TileE`, `TileN`, **`chartData C k : ChartData (4^k) (RTile C k)`** (definitions only) | **DONE (s4)** (defs) |
| `UncomputableNoiseDiagram/Chart/TheCA.lean` | `contentP`, `theCAOf`, **`theCA U`**, **`prop_2_1_theCAOf`**, **`theoremA_of_theCA`** (`(∀ U, Branches U (theCA U)) → TheoremA`) | **DONE (s4)**, strict |
| `UncomputableNoiseDiagram/Chart/RChart.lean` | `IsRChart`, `isDTiling`, `isQTiling`, **`word_apply`** (central words are the true words), **`phase_eq`** (decoded phase = (9), every phase), `phase_eq_zero_iff`, **`gate_iff`** | **DONE (s4)**, strict |
| `UncomputableNoiseDiagram/Chart/Board.lean` | Lemma 3.3: `strip_orient`, `endpoint_lt_of_interior`, **`board_row_walls`**, **`board_row`**, **`board_col_walls`**, **`board_col`**, **`board_active`** | **DONE (s4)**, strict |
| `UncomputableNoiseDiagram/Chart/BoardGaps.lean` | Lemma 3.3, laminar argument: `exists_gap`, **`laminar_gap`** (generic in the axis), **`board_not_vcarrier`**, **`board_not_hcarrier`** | **DONE (s4)**, strict |
| `UncomputableNoiseDiagram/Chart/BoardFlags.lean` | Lemma 3.3, exact flags: `flag_first`, `flag_second`, **`board_flags_row`** (`f_W = [x = L_*+1]`, `f_E = [x = R_*-1]`), **`board_flags_col`** | **DONE (s4)**, strict |
| `UncomputableNoiseDiagram/Chart/BoardTableau.lean` | Lemma 3.3, channels and recursion: `channel`, `board_hchannel`, `board_vchannel`, **`board_record`** (records obey (10); no HALT), **`board_init`**, **`board_step`**, **`board_vlink`**, `board_bottom`, `board_top` | **DONE (s4)**, strict |
| `UncomputableNoiseDiagram/Chart/Input.lean` | M4, **Lemma 4.2** (every phase): `prank_of_half`, **`prank_left`** (`ν₂(⌊t/2⌋)` before the centre), **`prank_center`** (`2d`), **`prank_right`**, `not_isFree_of_mod`, **`free_left_rank`**, **`free_right_rank`** (noncentral free ranks zero or odd), **`free_rank_even`** (`d ≤ a`), **`initial_zero`** (`d > a`: `t = 4^a` free of rank `2a-1`, earlier free ranks `≤ 2a-3`), **`count_initial_zero`** (index `2^{a+1}-2`), `chi2_eq`, `cutoff_of_flags`, **`input_read_large`**, **`input_read_small`** | **DONE (s5)**, strict |
| `UncomputableNoiseDiagram/Machine/Run.lean` | M2, **Lemma 4.1(a)**: `nextRow`, `oneHead`, **`nextRow_stay/up/down(_fail)`**, `PCfg`, `stepU`, `stepB`, `colOf`, **`nextRow_colOf`**, **`runP_eq`**, `stepB_iterate`, **`stepB_iterate_eq`**, absorbing FAIL/HALT | **DONE (s5)**, strict |
| `UncomputableNoiseDiagram/Machine/Scan.lean` | M3, Lemma 4.1(b), first part: single steps, `head_iterate_le`, `Reaches`, `move_up/down`, `scan_up`, `ret_home`, absorption (`not_halt_before`, `never_halt_of_fail`), **forgetting the input tracks** (`program_forget`, **`iterate_forget`**, D30), SCAN (`scan_phase`, **`scan_plus`**, **`scan_guard`**, **`scan_forever`**), RUN simulates `U` (`wt`, `sim`, `sim_step`, `sim_step_none`, **`sim_inv`**, **`sim_halts`**, **`sim_no_halt`**) | **DONE (s5)**, strict |
| `UncomputableNoiseDiagram/Machine/Passes.lean` | M3, Lemma 4.1(b), second part: transitions after SCAN, `plus_phase`, **`pass_block`**, **`pass_blocks`**, **`halving_step`**, `halving_all`, `halving_last`, **`skip_phase`**, **`copy_step`**, `copy_all`, `copy_last`, **`reaches_run`** | **DONE (s5)**, strict |
| `UncomputableNoiseDiagram/Machine/Decode.lean` | M3, **Lemma 4.1(b)** (D29): `Decodes`, `forget_scan`, **`decode_halts`** (one time `T` for all input tracks above `j_*`), **`decode_no_halt`**, **`guard_no_halt`**, on the board **`runP_no_halt`**, **`runP_halts`**; the read-only tracks are never written (`program_tracks`, `deltaP_tracks`, `stepB_tracks`, **`runP_tracks`**) | **DONE (s5)**, strict |
| `UncomputableNoiseDiagram/Chart/BoardRun.lean` | S8, Lemma 3.3 indexed (D27): `FreeOff`, `Nd`, **`count_freeOff`** (`N_d`), `card_freeOff`, `freeAt` (`Nat.nth`), `freeAt_zero`, `freeAt_last`, `freeAt_lt`, `freeAt_consec`, `boardH`, `boardPi`, **`board_run`** (the record at `(x_i, y_j)` carries `runP i j`) | **DONE (s5)**, strict |
| `UncomputableNoiseDiagram/Chart/Halting.lean` | M6, **Prop 4.3, halting branch** (every phase): `IsBottomEnd`, `prank_frameLo`, `isEnd_of_bottomEnd`, **`bottomEnd_gate`**, **`chart_wrong_flag`** | **DONE (s5)**, strict |
| `UncomputableNoiseDiagram/Chart/NonHalting.lean` | M5, Prop 4.3 nonhalting, first part (every phase): `prankOf`, `cutH`, `cutPi` (board inputs under the cutoff `[r < cut]`), **`board_no_halt`** (`cut ∈ {2a-2, 2a-1}`, `U(n)` nonhalting: no board of any depth halts), **`board_run_no_halt`** | **DONE (s5)**, strict |
| `UncomputableNoiseDiagram/Chart/Construct.lean` | M5, **Prop 4.3 nonhalting, one typical phase** (D31, D34): `freeAt_eq_zeta`, `dqOf`, **`dqOf_spec`** (Lemma 3.2 as a definition), `HSegM`/`VSegM`/`GPosM` (channels and board sites with the row frame named) and uniqueness, `sAt` (board contents), `hcolF`/`vcolF`/`recF`, `lEm`/`lNm`/`kFm` and their values at board sites, `rawVal`/`rawOf` (routing fields from `UPD.BG.cfg`), (O1)–(E3) from `UPD.BG.cfg_O1 … cfg_E3`, `raw_K1`, `raw_K2`, **`raw_rules`** ((C0) and the tableau (10): no HALT, read-only tracks), `raw_K3`, `raw_allowed`, `raw_tileOK`, `raw_tileE`/`raw_tileN`, `NHalt`, `toTile`, **`chartOf`**, **`chartOf_isRChart`**, `chartOf_phase`, `chartOf_V`, `chartOf_H`, **`chartOf_bottom_flag`** | **DONE (s6)**, strict |
| `UncomputableNoiseDiagram/Chart/ChartLaw.lean` | M5, **Prop 4.3 nonhalting, the TI law** (D32): covariance under `τ ↦ τ + a` (`dig_shift`, `prankOf_shift`, `FShift`, `isFree_shift`, `zeta_shift`, `PShift.cutH_eq`/`cutPi_eq`/`sAt_eq`, `runP_congr`, `wdL_shift`, `wdR_shift`, `wtag_shift`, `evTag_shift`, `PTrans.*` for every field), **`chartOf_shift`**; D31: **`measurableSet_typical`**, **`haar_typical`**; measurability (`mlevel_*`, `measurable_chartOf`); `chartLaw`, **`chartLaw_shift`**, `GoodChart`, `measurableSet_goodChart`, `goodChart_chartOf`, `ae_goodChart`, **`chart_law_exists`** | **DONE (s6)**, strict |
| `UncomputableNoiseDiagram/Contour/Coherence.lean` | C3, **Lemma 5.3** (D33): the pairing (13) (`PSrc`, `pHi`, `pLo`, `provOff_pair`, **`exists_pair`**), `sep`, `sep_step`; `MarkedAt`, `TwoCl`, `IsFlagTraj`, `MClosed`, `UL`; `UL.drvA`, `card_marked_le`, `card_failed_le`; **`coh_rel`**, **`coherence_eq`**, **`coherence_compat`**, `coh_back`, `coh_persist`, `coh_cover`, **`coherent_chart`**; `markedFrom`, `marked` (the raw marked set `𝓜`), **`marked_closed`**; **`isFlagTraj_of_complete`**, **`coherence_complete`** (for the complete trajectories of `ruleCA`) | **DONE (s6)**, strict |
| `UncomputableNoiseDiagram/Contour/RawPaths.lean` | C2, **Lemma 5.2** (D35): space-time points `Pt`, ordinary steps (`par`, `OrdStep`), the graph `nbr` (degree `≤ 18q`); the marked derivation of `𝓜^{t₀}` as a `GroupedSystem` (`MF`, `pd`, `sel`, **`sys`**, potentials `psi`, `psi_par`, **`isPotential_psi`**); contours (`IsContour`, `exists_contour_nf`, **`exists_contour`**: `f` flags, `85e ≤ 4000(f-1)`, slab `[t-e,t]`, `≤ e` ordinary-step edges); the path argument (`pathEdges`, `connectedAt_union`, **`exists_cover`**: `m ≤ 50f`, `≤ 101f` edges); `noiseLaw₂_flags_eq`, `flags_measure`, **`measure_le_tsum_from`** (Lemma 9.1 from `G` on), `PathEv`, `pathEv_null`, **`raw_paths`**, **`raw_paths_threshold`** | **DONE (s7)**, strict |
| `UncomputableNoiseDiagram/Contour/Deep.lean` | C4, **Lemma 5.4** (D36): `exists_two_clusters` (`> K` providers occupy two clusters), `chk_center`; the context `Ctx` (flags, data `D_s`, chart), `depth`, `NFv`/`NFa`, `ChildOK`, `pdD`, `supD`, the rank `rkD`, **`sysD`** (virtual levels at bookkeeping times `s + j` over the marked derivation), **`isPotential_psiD`**, `inv_reach`, `flag_of_termD`, `gBin_add_level` (every arm crosses every level); the deep graph `nbrD` (degree `≤ 36q`), `IsDeepContour`, **`exists_deep_contour`**; `qRoot`, `ctxOf`, **`deep_wrong`** (`f ≥ 11`, `e ≤ 50(f-1)`, `T ≤ e`, flags in `[t - e, t - 1]`), **`deep_wrong_lag`** | **DONE (s7)**, strict |
| `UncomputableNoiseDiagram/Sensors/Tails.lean` | N3, **Lemma 6.2, the probabilistic core** (D37): `mgf_le_of_zero_one` (`1 - p + pe^t ≤ exp(p(e^t-1))`), **`chernoff_zero_one`**, **`chernoff_ratio`** (`t = log(θ/p)`); numerics `log_75_53` (`log(75/53) ≥ 11/32`, Taylor bound of `exp`), `log_four_gt`, **`short_exponent`** (`θ log(θ/p_r) - θ + p_r ≥ .03C + rC/3`), `exp_neg_le_two_zpow` (`e^{-x} ≤ 2^{-⌊x⌋}`); **`short_tail`** (`≤ 2^{-⌊3nC/100⌋}(2^{-⌊nC/3⌋})^r`), **`hoeffding_zero_one`**, **`long_tail`** (`≤ 2^{-⌊nC²/50⌋}`); `geom_three_le`, `lower_law_gt` (`.98(1-(1-ε)^W) > .9C`), `ell_cast`, `short_support_lt` (`ε(ℓ_d+1) < .53C4^{-r}`), `uB_cast`, `zB_cast`, `wB_cast`, `etaHat_cast`, **`eta_bound`** (the union over a bin `≤ η̂_B`) | **DONE (s7)**, strict |
| `UncomputableNoiseDiagram/Sensors/Ideal.lean` | N1, **the ideal experiments and the laws (14), (15)** (D38): `DetBy`, `extend`, **`infinitePi_inter_eq_mul`** (events determined by disjoint finite coordinate sets are independent); `RideEv` (the most recent replacement along distinct atoms exists and its mark satisfies `g`), `measurableSet_rideEv`, `detBy_rideEv`, `infinitePi_coord`, **`rideEv_real`** (`ρ(1-(1-ε)^n)`); `upMark`, `loMark`, `uniformLaw_fieldSet`, `uniformLaw_upMark` (`99/100`), `uniformLaw_loMark` (`98/100`), **`upper_law`** (14), **`lower_law`** (15) | **DONE (s7)**, strict (see the audit line below) |
| `UncomputableNoiseDiagram/Sensors/Ownership.lean` | N2, **Lemma 6.1** (D39): `detBy_mono`, `detBy_biInter`, `detBy_biUnion`, `measurableSet_of_detBy`, **`infinitePi_biInter_eq_prod`**, **`iIndepFun_of_detBy`** (independence on pairwise disjoint finite coordinate sets); characteristics (16): `vP`, `chSite`, `laneAtom`, `laneAtom_inj`; true rides `ride` (`ride_length`, `ride_nodup`, `mem_ride`, `ride_disjoint`); `IsGate`, `IsGate.lanePhase`, `isGate_of_end`, **`phaseZero_block`** (phase-zero rows own disjoint blocks of `B` rows), `depth_unique`, `rightEnd_dvd`, `rightEnd_eq`, `ell_lt_four_pow`, **`ownership`**, `gateAtoms`, `mem_gateAtoms`, **`gateAtoms_disjoint`** | **DONE (s8)**, strict |
| `UncomputableNoiseDiagram/Sensors/Gate.lean` | N3 at one gate (D40): `PNoise`, `laneCount`, **`ShortBad`**, **`LongBad`**, `laneCount_congr`, `detBy_shortBad`, `detBy_longBad`, `laneInd`, `lanes_iIndep` (Lemma 6.1: independent lanes), `upper_mean_le`, `shortBad_le_of`, `longBad_le_of`, `pLaw` (the two-sided noise law on `PNoise CD`), `pLaw_eq`, `isProbabilityMeasure_pLaw`, **`shortBad_le`** (`≤ u_B z_B^r`), **`longBad_le`** (`≤ w_B`) | **DONE (s8)**, strict |
| `UncomputableNoiseDiagram/Sensors/Joint.lean` | N4, **Lemma 6.3** and Lemma 6.2 per bin (D40): `biInter_union_subset`, `exists_big_class`, `min_le_sqrt_mul`, `real_biInter_eq_prod`, **`joint_bound`** (abstract Lemma 6.3); `isRightEnd_iff`, `card_ends_le`, `Label`, `rawList`, **`RawEv`**, `rawSupp_disjoint`, `rawEv_le` (`≤ εW`), `Regime`, `ell_mono`, `GateBad`, `gateLen`, **`StatEv`**, `statSupp`, `gateAtoms_sub_statSupp`, `detBy_statEv`, **`statSupp_disjoint`** (residue classes mod 3), **`statEv_le`** (Lemma 6.2: a bin `≤ η̂_B`), **`joint_source_bound`** | **DONE (s8)**, strict |
| `UncomputableNoiseDiagram/Sensors/Selected.lean` | Section 6 at the selected parameters: **`Bparam_eq`** (`B = 4^k`, kernel-safe), `cden_ge`, `C_le_hundredth`, `C_real_eq`, **`regime_final`** (every `ε ∈ I_n`), **`joint_source_final`** (Lemma 6.3 with `γ = gammaOf (4^k)`) | **DONE (s8)**, strict |
| `UncomputableNoiseDiagram/Memory/Count.lean` | Mem3, **Lemma 7.2, the combinatorial core** (D41): `prop_of_mem_filter`, **`grpEdges_card_le_lin`** (group links `≤ |C|²|P|`), `armEdge_step`, `grpEdge_spec`, **`mem_contour`** (`≤ 167g` edges), `reach_image`, `reach_filter_not_diag`, `MemEnc`, `prepend`, `mem_encoding_nonUN`, `MemEnc.mono`, `MemEnc.isEncoding`, **`mem_encoding`** (every root, `≤ 256g` edges, `g` distinct labels), **`UND.Memory.mem_union`** (the union bound against the joint source law) | **DONE (s8)**, strict |
| `UncomputableNoiseDiagram/Memory/Ride.lean` | Mem2, **the helper ride** (D42; also for Lemma 8.1): `flagAt`, `markAt`, `HelperTraj`, `rep_field`, `rideVal`, `rideVal_append`, `ride_succ`, `rideEv_up_iff`, `rideVal_of_rideEv_lo`, `chSite_sub_jy`, `chSite_pred`, `chSite_add_jy`, `laneAtom_eq`, `LiveAt`, `copy_step`, `origin_step`, **`ride_copy`**, **`ride_short`**, **`gate_J`**, `mem_filter'`, **`hcount_short`** (`h_w` = upper successes), **`lcount_long`** (`l_w ≥` lower successes) | **DONE (s8)**, strict |
| `UncomputableNoiseDiagram/Memory/Derivation.lean` | Mem2/Mem3, **Lemma 7.1 as a grouped derivation** (D43): `val` (data at level `0`, `F_R^j(D_{t-j})` at level `j`), `aV`, `qV`, `rideBase`, `chiOf`, `outT`, `psi_eq_chi`; `MCtx`, `Bad`, `Link`, `NFv`, `NFd`, `UNd`, `supOf`, `PGood`, **`exists_pgood`** (more than `K` failed checks, each with a bad Moore input, two clusters), `rkM`, **`sysM`**, **`isPotential_sysM`**, `hgrp_sysM`, `hUUU_sysM`; the projection `fM` and graph `nbrM` (**`card_nbrM_le`**: `≤ 108q + 6 ≤ Δ`), **`step_nbr`**, `bad_of_reach`; `Hyp`, **`term_source`** (a reached terminal is a flag (raw source) or an erasure at a correct gate with its intrinsic bad event (statistical source)), **`mem_cover`** (Lemmas 7.1–7.2 at every data error) | **DONE (s9)**, strict |
| `UncomputableNoiseDiagram/Memory/Error.lean` | `RM`, `SM`, **`joint_MP`** (Lemma 6.3 on projected labels), `gamma_facts`, `tsum_ofReal_mem`, **`mem_bad_le`** (a data error has probability `≤ S = Σ_{g≥1}(K_mem γ)^g < 1/4`, for any trajectory family satisfying `Hyp`) | **DONE (s9)**, strict |
| `UncomputableNoiseDiagram/Memory/RefChart.lean` | Mem1, the reference chart (D44): `blockAt`, `liftSym`, `liftChart`, `liftSym_eq`, `ctr_liftChart`, **`liftChart_full`**, `leftEnd_back`, **`chart_gate`** (gates of the chart of a typical phase: depth `d ≥ k`, row flag `[d < a]`, origin exactly `ℓ_d` back) | **DONE (s9)**, strict |
| `UncomputableNoiseDiagram/Memory/Init.lean` | Mem1, the stationary helper initialization (D42, D45): `firstHit`, `firstHit_cons`, `firstHit_map`, **`measurableSet_firstHit`**, `chainSite`, `ogOf`, `initField'`, `initField`, `initCfg`, **`initField_rec`**, `encodeConfig`, `posPart`, `negPart`, `pastN`, `X0`, **`hyb`** (the hybrid trajectory), **`hyb_succ`**, **`hyb_hyp`** (the hypotheses of Lemma 7.1 for every noise) | **DONE (s9)**, strict |
| `UncomputableNoiseDiagram/Memory/InitLaw.lean` | Mem1, the initial law (D45): **`measurable_X0`**, **`X0_shift`**, `initLaw`, `isProbabilityMeasure_initLaw`, **`initLaw_TI`**, `glue`, **`glue_law`** (negative- and positive-time noise glue to the two-sided noise law; `Measure.eq_infinitePi` on boxes), `encode_hyb`, **`law_initLaw`** | **DONE (s9)**, strict |
| `UncomputableNoiseDiagram/Memory/Theorem.lean` | Mem4, **Theorem 7.3** (D46): `Smem`, **`law_initLaw_le`** (Fubini over the chart parameter), `cutOf`, `nhalt_cutOf`, `cSf`, `measurableSet_cSf`, `cSf_shift`, **`memLaw`**, `memLaw_prob`, **`memLaw_TI`**, `hyp_typical`, `law_memLaw_le`, `liveOne`, `mem_cyl_liveOne`, **`memory_branch`** (the memory clause of `Branches` for `theCA U`), **`theorem_7_3`**, **`theoremA_of_halting`** (Theorem A from the halting branch alone) | **DONE (s9)**, strict |
| `UncomputableNoiseDiagram/Forget/Miss.lean` | F1, **Lemma 8.1**: `helperTraj_of_complete`, `data_of_complete` (s9); monotone rides (s10): `isub` (inclusion of represented intervals), `GoodAt` (monotone drivers: `A = ⊥`, or `Q = ⊥`, or `Q` live with a given origin status), `mono_step`, `mono_origin`, **`ride_mono`**, **`ride_mono_short`**, **`lcount_le_short`** (`l_w ≤` upper successes), **`lo_le_hcount`** (lower successes `≤ h_w`), **`missed_erasure`** (Lemma 8.1, deterministic, every trajectory with `HelperTraj`) | **DONE (s10)**, strict |
| `UncomputableNoiseDiagram/Forget/Gate.lean` | F1, chart part: **`isRChart_ctr`** (the central tiles of a full legal chart form an `R`-chart), `gate_facts`, **`halting_gate`** (Prop 4.3 halting branch read by the controller, every phase: an `End` with lane phase zero, row flag `hb`, origins exactly `ℓ_d` back, `d = a - 1` or `a`) | **DONE (s10)**, strict |
| `UncomputableNoiseDiagram/Forget/History.lean` | F2, **Lemma 8.2 probabilistic core** (D48): nodes, blocks (`Blk`), `nxt`, `DFlags`, `valid`, `ok`, `badSet`, `flagSet`, `WEv`, `wt`; `flagSet_time`, `card_flagSet` (disjoint slabs), `wt_eq`, **`measure_badSet_le`** (independence at distinct times), `le_mul_pow_three` (Hölder `min(x⁴, y⁴) ≤ x y³`), **`measure_WEv_le`**, **`tsum_wt_le`** (`≤ β^r`), `DeepC`, **`HPath`**, `path_disp`, **`exists_witness`**, `card_boxP`, `card_flagSets_le`, **`blk_sum_le`**, **`hpath_null`** | **DONE (s10)**, strict |
| `UncomputableNoiseDiagram/Forget/HistBase.lean` | Q5, **the history bases (22) of Prop 9.2**: `pow_four_le`, **`term_le`**, `sqrt_sqrt_facts`, **`hist_base`** (block weights `< 1` with `α = (64K)^{-1}`, `γ = ε^{1/4}`, `ε ≤ (64K)^{-44}`, `Wε ≤ 1`) | **DONE (s10)**, strict |
| `UncomputableNoiseDiagram/Forget/Eliminate.lean` | F2, **Lemma 8.2** (D49): `flagE`, `badK`, `atomsK`, `rootK`, `chSite_node`, `detBy_badK`, `atomsK_disjoint`, **`uld_back`**, `GateOracle`, **`node_prop`** (Lemma 8.1 + Lemma 5.4 at one vertex), **`hpath_of_ul`**, **`no_ul_generic`** (a.s. no unmarked live reading in any complete trajectory) | **DONE (s10)**, strict |
| `UncomputableNoiseDiagram/Forget/Coupling.lean` | F3–F4, **Lemma 8.4** via the raw set (D50, F21): **`proposal_of_dead`**, **`live_marked`**, **`disc_step`**, `flagged_complete`, the coupling graph `bigNbr`, `conNbr`, `nbC` (`card_nbC_le`, `nbC_symm`, `degree_le_rare`), `conEdge`, **`exists_cover_C`**, `DiscEv`, **`discEv_null`** (`K_rare ε < 1`), **`coupling_generic`** | **DONE (s10)**, strict |
| `UncomputableNoiseDiagram/Forget/Halting.lean` | F4, Q5, Q7 (D51): **`gateOracle_theCA`**, `Khist_facts`, **`halting_branch_gen`** (variables `n₀`, `k`, `s`), **`gate_bounds_final`** (`ρ_B ≤ η̂_B` at a single critical gate), `eta_final`, `eps_hist_final`, `rare_of`, `rare_final`, **`halting_branch`** (the hypothesis of `theoremA_of_halting`) | **DONE (s10)**, strict |
| `UncomputableNoiseDiagram/Assembly.lean` | Q7 hook: `Branches U A` (the two branch statements), `window_rate`, **`noiseDiagram_of_branches`**, **`theoremA_of_branches`** | **DONE (s3)**, strict |
| `UncomputableNoiseDiagram/AuditCommand.lean`, `Audit.lean` | `#audit_axioms(_strict)`, `#audit_prefix`; the audit | builds |
| `UncomputableNoiseDiagram.lean` | root | builds |

Reused libraries load from prebuilt oleans (read only): `FixedNoiseErgodicity.Statements`,
`FixedNoiseErgodicity.Section2.Process`, `FixedNoiseErgodicity.Combinatorics.EdgeCount` (FNE),
`UndecidablePhaseDiagram.Statements`, `UndecidablePhaseDiagram.Scaffold.Tower`,
`UndecidablePhaseDiagram.Compiler.Universal`, `UndecidablePhaseDiagram.Background.BgMap` (UPD; from
session 6, for `UPD.BG.cfg` and its lemmas, `ae_typical_addDig`, the `MLevel` calculus).

## Sorry census

`scripts/sorry_census.py`: **0** `sorry` tokens in 74 files (session 10; `UND.theorem_A` closed).
Forbidden constructs: none (`lint ok`). Axiom-level census (`#audit_prefix UND`, **3615**
declarations): none depends on `sorryAx`, none uses a disallowed axiom. `AXIOMS.txt` is the audit
log (AUDIT OK, no errors).

## Axioms of the proved declarations (from `AXIOMS.txt`)

**1166** `#audit_axioms_strict` commands in `Audit.lean` (session 10): the three final targets
`UND.theorem_A`, `UND.corollary_9_4`, `UND.one_rule_undecidable` (strict since session 10:
`[propext, Classical.choice, Quot.sound]`) and **1163** proved leaves (73 new in session 10), every one
within `propext`, `Classical.choice`, `Quot.sound`:

| group | leaves |
|---|---|
| Corollary 9.4 and the one-rule corollary (`Corollary.lean`) | 6 |
| the intervals (17) (`Windows.lean`) | 13 |
| geometry and exact constants (`Parameters/Geometry.lean`) | 29 |
| the search (25) (`Parameters/Search.lean`) | 27 |
| black type and the cutoff lemma (`Chart/BlackType.lean`) | 8 |
| P1–P3 (`PCA/Process.lean`, `PCA/Markov.lean`) | 30 |
| P4–P7 (`PCA/Cylinder.lean`, `Feller.lean`, `Translation.lean`, `ForgetErgodic.lean`) | 57 |
| Q3 and the interval clauses of Prop 9.2 (`Parameters/Threshold.lean`) | 28 |
| C1, Lemma 5.1 (`Contour/Grouped.lean`) | 75 |
| P8, P9, F5, Lemma 8.5 (`PCA/Pullback.lean`, `PCA/Attraction.lean`) | 21 |
| Q5, series bases of Prop 9.2 (`Parameters/Bases.lean`) | 10 |
| Q4, Lemma 9.1 and the witness hook (`Contour/Counting.lean`) | 26 |
| R1–R6, Prop 2.1 (`Rule/Checker.lean`, `Proposal.lean`, `CA.lean`, `Noise.lean`) | 44 |
| S1 wiring, S5 and S6 arithmetic (`Chart/LanePhase.lean`, `Chart/Walls.lean`) | 8 |
| Q7 hook (`Assembly.lean`) | 3 |
| S6, S8 first step (`Chart/Origins.lean`) | 8 |
| S3, S4, Lemma 3.2 (`Chart/Decorated.lean`) | 13 |
| S5 decoder (`Chart/PhaseTable.lean`) | 7 |
| `theCA`, Prop 2.1 for it, Theorem 9.3 hook (`Chart/TheCA.lean`) | 2 |
| legal `R`-charts (`Chart/RChart.lean`) | 12 |
| Lemma 3.3 (`Chart/Board.lean`, `BoardGaps.lean`, `BoardFlags.lean`, `BoardTableau.lean`) | 36 |
| D17 variant (`Contour/Counting.lean`: `gLen_le_three_gBin`, `pLen_le_three_pBin`) | 2 |
| M4, Lemma 4.2 (`Chart/Input.lean`) | 24 |
| M2, Lemma 4.1(a) (`Machine/Run.lean`) | 18 |
| M3, Lemma 4.1(b) (`Machine/Scan.lean`, `Passes.lean`, `Decode.lean`) | 94 |
| Lemma 3.3 indexed (`Chart/BoardRun.lean`) | 13 |
| M6, Prop 4.3 halting (`Chart/Halting.lean`) | 4 |
| M5 groundwork: read-only tracks (`Machine/Decode.lean`) | 5 |
| M5 first part: no board halts (`Chart/NonHalting.lean`) | 4 |
| M5, the chart of a typical phase (`Chart/Construct.lean`) | 52 |
| M5, covariance, measurability, the TI chart law, D31 (`Chart/ChartLaw.lean`) | 80 |
| C3, Lemma 5.3 and the raw marked set (`Contour/Coherence.lean`) | 29 |
| C2, Lemma 5.2 (`Contour/RawPaths.lean`) | 42 |
| C4, Lemma 5.4 (`Contour/Deep.lean`) | 27 |
| N3, Lemma 6.2 probabilistic core (`Sensors/Tails.lean`) | 20 |
| N1, the ideal experiments, (14), (15) (`Sensors/Ideal.lean`) | 16 |
| N2, Lemma 6.1 (`Sensors/Ownership.lean`) | 22 |
| N3 at one gate (`Sensors/Gate.lean`) | 15 |
| N4, Lemma 6.3, Lemma 6.2 per bin (`Sensors/Joint.lean`) | 20 |
| Section 6 at the selected parameters (`Sensors/Selected.lean`) | 6 |
| Mem3, Lemma 7.2 combinatorial core (`Memory/Count.lean`) | 13 |
| Mem2, the helper ride (`Memory/Ride.lean`) | 17 |
| Mem2/Mem3, Lemma 7.1 as a grouped derivation, Lemma 7.2 instance (`Memory/Derivation.lean`) | 47 |
| Lemmas 7.1, 7.2, 6.3: the data error bound (`Memory/Error.lean`) | 4 |
| Mem1, the reference chart (`Memory/RefChart.lean`) | 6 |
| Mem1, the stationary helper initialization, the hybrid trajectory (`Memory/Init.lean`) | 16 |
| Mem1, the initial law (`Memory/InitLaw.lean`) | 12 |
| Mem4, Theorem 7.3, the memory branch (`Memory/Theorem.lean`) | 17 |
| F1, Lemma 8.1: complete trajectories, monotone rides, the missed-erasure implication (`Forget/Miss.lean`) | 15 |
| F1, the wrong critical gate of every full chart (`Forget/Gate.lean`) | 3 |
| F2, Lemma 8.2 probabilistic core (`Forget/History.lean`) | 17 |
| Q5, the history bases of Prop 9.2 (`Forget/HistBase.lean`) | 4 |
| F2, Lemma 8.2 (`Forget/Eliminate.lean`) | 7 |
| F3–F4, Lemma 8.4 via the raw set (`Forget/Coupling.lean`) | 20 |
| F4, Q5, Q7, the halting branch for the automaton (`Forget/Halting.lean`) | 9 |

Smaller axiom sets: `[]` — `UND.Chart.black_child_*` (4) and seven structural lemmas of
`UND.Contour.GroupedSystem` (`isTerm_of_not`, `not_NF_of_UN`, `reach_sup`, `reach_un`,
`term_of_isTerm`, `term_of_sup`, `term_trans`); `[propext, Quot.sound]` — `UND.Chart.chain_black`,
`black_rank_compare`, `UND.Contour.GroupedSystem.rk_induction`, `UND.Param.rare_degree_lt`;
`[propext]` — 23 kernel-arithmetic facts of `UND.Param` (as in session 1) and four of session 3
(`UND.Counting.enc_term`, `UND.Rule.Helper.rep_repr`, `UND.Chart.lanePhase_succ`,
`UND.Chart.four_pow_eq`). Everything else:
`[propext, Classical.choice, Quot.sound]`, including **`UND.theorem_A`, `UND.corollary_9_4`,
`UND.one_rule_undecidable`** (session 10). No declaration depends on `sorryAx`.

## Statement fidelity

**Source (QB, s10):** the formal targets match v1.1.0 (released, DOI 10.5281/zenodo.24152233), whose
Theorem A, Theorem 9.3 and Corollary 9.4 are byte-identical to v1.0.0's; the deviations FD1, FD2 and
the Prop 2.1 count, printed in v1.0.0, are corrected in v1.1.0 and are kept below as history.

How each definition of `Statements.lean` matches the paper (Section 2, Theorem A, Theorem 9.3,
Corollary 9.4) and the forgetting core's definitions. **[choice]** items were put to QB; all
were ACCEPTED in session 2 (see "Rulings (QB, session 2)" above).

* **F1 The lattice `ℤ⁶`.** `UND.Site 6 = Fin 6 → ℤ`. The paper's `(u, P) ∈ ℤ² × ℤ⁴` is an
  identification inside the proof (D5). FNE writes `Site k = ℤ² × (Fin k → ℤ)`; same lattice,
  different presentation; FNE's type is not reused because its whole layer is tied to the quorum
  rule. **[choice]**
* **F2 Cellular automaton.** `UND.CA d`: `numSymbols > 0`, alphabet `Fin numSymbols`, a finite
  neighbourhood `nbhd : Finset (Site d)`, a local function `(nbhd → Fin numSymbols) → Fin
  numSymbols`; `apply x w = f((x(w + z))_{z ∈ N_F})`. Paper, Section 2: "a map `F` given by one
  finite neighbourhood `N_F` and one function `f : Σ^{N_F} → Σ`" — exact; the finite alphabet is
  presented as `Fin |Σ|` **[choice]**. FNE has no generic CA: its `quorumRule k R` is one rule, and
  its `IsPositiveRatePCA` clauses (i) translation commutation and (ii) locality are properties to
  prove; here they hold by construction.
* **F3 Uniform whole-symbol replacement.** Flags `E_t(w)` with law `FNE.flagLaw ε` (reused
  verbatim: `ε δ_true + (1 - ε) δ_false`), values `Z_t(w)` with law `uniformLaw = |Σ|⁻¹ • count`
  (FNE's `uniformSym`, for `Fin |Σ|`), all independent (`Measure.infinitePi` over
  `ℕ × Site d`, as FNE's `noiseLaw`); `update`: the entire symbol is replaced where the flag is
  set, else `F(X_{t-1})(w)` (paper's displayed update). Time starts at `0`, noise index `t` drives
  the step to time `t + 1` (FNE's convention) **[choice]**.
* **F4 Law and stationary law.** `law ε μ t = (μ ⊗ noise).map (run · · t)` (FNE's `law`);
  `IsStationary ε μ ↔ law ε μ 1 = μ` (FNE's `IsInvariant`). Paper: "A stationary law is fixed by
  this Markov kernel." Exact.
* **F5 Ergodicity.** `IsErgodic ε`: a stationary probability `π`, the only stationary probability,
  with `law ε μ t → π` weakly for every probability `μ`, weak convergence being
  `FNE.WeakTendsto` (bounded continuous functions; product topology of the discrete alphabet).
  Same shape as `FNE.IsErgodic`. Paper: "Ergodicity means a unique stationary law and weak
  convergence to it from every initial law." Exact.
* **F6 Translation invariance.** `IsTranslationInvariant μ ↔ ∀ a, μ.map (shift a) = μ`,
  `shift a x = x(· + a)`. Paper: "invariance under every spatial translation." Exact (all `a`, so
  the sign of the shift is immaterial; UPD's `IsTranslationInvariantMeasure` uses `x(· - a)` on
  `ℤ²`). FNE has no such statement-level notion.
* **F7 "At least two translation-invariant stationary laws."** `HasTwoTIStationaryLaws`: two
  distinct probability measures, both stationary and translation invariant. Exact.
* **F8 Pullback clause** (Thm 9.3, last sentence; Lemma 8.5). Two-sided noise `ℤ × Site d`, law
  `noiseLaw₂` (same factors), `flow ω s n x` = state at time `s + n` from `x` at time `s`,
  `pullback ω j x = Ψ_{-j,0}(x)`. `PullbackEventuallySingleton`: for every finite window `O`, almost
  surely there is `j₀` with all starts agreeing on `O` at time `0` for every `j ≥ j₀`, i.e. the
  projection of `K_j = Ψ_{-j,0}(Σ^{ℤ⁶})` to `O` is one point. (Since there are countably many
  windows, "for every `O`, a.s." is equivalent to "a.s., for every `O`".) **[choice]** of
  rendering.
* **F9 "Computably specified".** Not rendered (D11 in `BLUEPRINT.md`): for a fixed `U` the automaton
  is one finite object and the adjective has no formal content. **ACCEPTED (QB, s2)**: keep; no
  computable family `U ↦ A_U` (`TheoremA` holds for every machine `U`, which is stronger).
* **F10 Computable disjoint rational open intervals.** `IsWindowFamily lo hi`: endpoints `lo n`,
  `hi n : ℚ` with computable presentations `n ↦ (p, q)`, `q > 0`, `p/q` (the hard-model core's
  `CorollaryB` convention); for `n ≥ 1`: `0 < lo n < hi n < 1`; `I_n = Set.Ioo (lo n) (hi n)` in
  `ℝ`; pairwise disjoint for distinct `n, m ≥ 1`. The bounds `0 < lo`, `hi < 1` make "rates"
  explicit (the paper's intervals lie in `(0, ε_*)`) **[choice]**.
* **F11 The universal machine `U`.** `UPD.Machine` (reused): one-way tape (cells `0, 1, …`), states
  `Fin (s+1)` with initial state `0` not halting, symbols `Fin (g+2)` with blank `0` and `1`,
  halting predicate, moves left/right; input `n` = cells `0 … n-1` hold `1`; a move left from
  cell `0` ends the run without halting; `HaltsOn U n`; `UPD.Universal U` = `{n ≥ 1 : U halts on
  n}` not computable. Paper: "a fixed deterministic one-way-tape universal machine on positive
  unary inputs … finite tape alphabet containing blank and 1 … absorbing FAIL, HALT distinct from
  its working states". Differences: no stay moves and a non-halting initial state are required of
  `UPD.Machine` (a universal machine never starts halting; stay moves compile away); an attempted
  left exit is non-halting in both. FNE's `TuringMachine` (two-sided tape, blank input) is not the
  paper's `U` and is not used.
* **F12 Theorem A / 9.3.** `TheoremA := ∀ U : UPD.Machine, ∃ (A : CA 6) (lo hi), NoiseDiagram U A lo
  hi`: the windows, and for `n ≥ 1`, `ε ∈ I_n`: ergodic iff `U` halts on `n`; non-halting ⇒ two TI
  stationary laws; halting ⇒ ergodic (unique stationary law attracting every initial law) and the
  pullback clause. Stated for every machine (the printed theorem fixes one universal `U`; the
  construction does not use universality) **[choice]**, as `UPD.TheoremA`. The quantifier order
  follows the printed one (`U` first); the paper's intervals are in fact independent of `U` (the
  development will exhibit them so).
* **F13 Corollary 9.4.** `CorollaryNineFour := ∀ U, Universal U → ∃ A lo hi, NoiseDiagram U A lo hi
  ∧ PromiseUndecidable A lo hi`; `PromiseUndecidable`: no computable `g : ℕ × ℕ → Bool` answers
  `IsErgodic (p.1/p.2)` correctly on every presentation `p` of a rate in some `I_n`, `n ≥ 1`
  **[choice]** (presentation of rationals as in F10). "For this fixed automaton" is the same `A`
  in both conjuncts.
* **F14 `OneRuleUndecidable`** (not separately printed; the sentence after Theorem A): one fixed
  `A : CA 6` and a window family on which ergodicity is promise-undecidable. Derived from
  Cor 9.4 and UPD's universal machine.
* **F15 Machine `P` (Section 4.1), prose renderings (D28, ACCEPTED by QB, s5).** Not statement
  level (Theorem A does not mention `P`), recorded for the reader of `Machine/P.lean`:
  (a) "a return to the origin with continuation `Z`" from a non-SETEND state is a *stay* move into
  `RET_Z` (SETEND moves left into `RET_{R_00}`, as printed); (b) `RUN_q` at a halting `q` enters
  HALT with a stay move; (c) a halting successor of `U` moves as `U` does and enters HALT, so a move
  off cell `0` fails, matching `UPD.Machine.step = none`; (d) a failing head at a tape end keeps the
  written symbol (`f_P` writes `δ_P`'s symbol and enters FAIL in place). None changes Lemma 4.1's
  statement; they fix its step counts.

* **F16 Lemma 4.1(b), the clause "any other positive count eventually fails"** (D29, CONFIRMED by
  QB, s6): printed intermediate clause not formalized (unused). Lemma 4.2 forces `j_* + 2 = 2^{a+1}`
  on every large board, so Prop 4.3 and Theorem A never use it.

* **F17 Prop 4.3, the translation-invariant chart law** (D32, CONFIRMED by QB, s7): proof-route
  difference. The printed proof takes a weak limit of spatial averages of one chart; the
  formalization pushes Haar measure forward along the equivariant map `τ ↦ chartOf τ`
  (`chartLaw`, `chartLaw_shift`, `chart_law_exists`). The printed statement is unchanged.

* **F18 Intermediate strengthenings** (QB, s8: intermediate lemmas may be stronger than printed
  when they imply the printed uses): Lemma 5.2 is proved for every `ε ∈ [0,1]` with `K_mem ε < 1`
  (printed: at the threshold; D35); Lemma 5.4 gives `f ≥ 12`, `e ≤ 48(f-1)` (printed `f ≥ 11`,
  `e ≤ 50(f-1)`; D36); Lemma 6.2 per bin counts at most `4^r` short ends and one long end (printed
  `3·4^r` and two; D40). Downstream uses consume the proved forms.

* **F19 Lemma 7.2 / Lemma 8.4, the group links** (D41, CONFIRMED by QB, s9): proof-route
  difference. The copied-arm witness keeps every link inside each group and counts them linearly
  (`≤ |C|²|P| = 25g`) instead of extracting the printed star sub-witness (`5g`); the encodings still
  feed exactly the printed union bounds (`≤ 256g` edges and `K_mem` for Lemma 7.2; `≤ 512g` and
  `K_rare` for Lemma 8.4). D14(b) is closed.

* **F20 Section 7, the stationary helper initialization** (D42, CONFIRMED by QB, s9): rendering.
  The initialization is the time-0 state of a hybrid trajectory on the two-sided noise (data and
  second coordinate held at the chart for `t ≤ 0`, helpers following (4) with the chart's drivers at
  every time, the automaton from time `0` on); the ideal field is the mark at the first flag or the
  reset at the first origin along the copy chain (`{0}` on the null event that neither occurs).
  The initial law is the push-forward of Haar phase ⊗ negative-time noise (the spatial average of
  the paper, as in F17), translation invariant by `memLaw_TI`.

* **F21 Lemmas 8.3–8.4, the live ordinary drivers** (s10, D50; for QB): proof-route difference.
  The printed proof bounds a live `A_t` by the rare-birth field `N^live` of Lemma 8.3 and covers the
  discrepancy path with grouped birth contours (`Ω = 7000`, `H₀ < 130`, `< 282g` edges, base
  `K_rare(N₀ε^M)^{1/16}`). The formalization bounds a live `A_t` by the raw set `𝓜` directly: by
  Lemma 8.2 every live data reading is in `𝓜`, so the `h > K` live checked centres of a live `A_t(z)`
  occupy two clusters and `z ∈ 𝓜` (`live_marked`); the discrepancy path is covered by the raw
  contours of Lemma 5.2 at the shifted anchors `w - j e_y`, with the proposal neighbourhood and the
  `B` planar shifts as literal edge labels (degree `≤ 18q + 2|N_F| + 2B ≤ Δ_rare`), at most
  `101f ≤ 512f` edges per `f` flags, into `K_rare^f` (Lemma 9.1, `card_encLe_KrareOf`'s bound), with
  base `K_rare ε < 1` (from `ε < ε_* ≤ [64K_rare(N₀+1)]^{-16}`). Lemma 8.4's statement is proved as
  printed (at time `0`, the form Lemma 8.5 consumes, D15). No birth contour is built, so v1.1.0's
  correction (iv) (the birth-contour clock) is not exercised; the constants `λ`, `M`, `N₀` enter only
  through `ε_*` (unchanged).
* **F22 Lemma 8.3 (rare births)** (s10): printed intermediate lemma not formalized (unused under
  F21). The printed statement is not needed by Theorem A.
* **F23 Lemma 8.2, the packing of the historical queries** (s10, D48; for QB): proof-route
  difference with the printed estimates. The witnesses are indexed by their number `r` of blocks (an
  intrinsic step, weight `α = (64K_hist)^{-1}`, `ρ_B ≤ η̂_B < α⁴`; or a deep contour with `f ≥ 11`
  flags, lag `ℓ ≤ W`, restart `W + 50(f-1) + 1` steps later at a displacement in `[0, 175·gap]⁴`,
  weight `γ^{3f}`, `γ = ε^{1/4}`); Hölder is used with the printed exponents (`ε^{3f/4}ρ_B^{m₀/4}`,
  as `min(x⁴, y⁴) ≤ x y³`); the `r`-block weights sum to at most `β^r`, `β < 1` (`hist_base`),
  instead of the printed `(f + m₀)`-indexed count `K_hist^{f+m₀}W^{6c}`; the base estimate uses
  `ε ≤ (64K_hist)^{-44}` and `Wε ≤ 1` exactly as the printed bases (22). The deep contours are
  consumed as proved (`deep_wrong_lag`: `f ≥ 11` from `f ≥ 12`, `e ≤ 50(f-1)` from `e ≤ 48(f-1)`,
  D36). The phase `φ` is replaced by the gate site and its kind (a countable union over the planar
  site, the kind and the root node), finer than the printed finite union over phases.
* **F24 Lemma 8.1 as formalized** (s10, D47): deterministic, for every trajectory whose helpers
  follow (4) (`HelperTraj`; every complete trajectory, `helperTraj_of_complete`), with the chart's
  gate entering through its controller readings (`End`, lane phase zero, row flag, origins exactly
  `ℓ_d` back); "a wrong live deep query at one prescribed lag `0 ≤ ℓ ≤ W`" is `∃ ℓ ≤ W`, the live
  `Q` at the lag-`ℓ` base of the base characteristic differing from the chart there.

## Fidelity deviations from the printed v1.0.0 text (all corrected in v1.1.0; history)

* **FD1 Lemma 5.1 (`lem:pole`), last sentence** (QB, session 2, after an external
  refutation-first audit). **Printed in v1.0.0; corrected in v1.1.0** (the formal target matches
  v1.1.0). As printed, "If support edges decrease time
  by one and group identifications preserve time, the span is at most `e`" is **false** when the
  permitted unary zero-potential links change time: the link `(P, t) ↦ (P + D·(32,32,32,32), t - D)`
  changes `ψ₀` by `5·4·32·D - 640·D = 0` and each `ψᵢ` by `-5·32·D + 160·D = 0` yet moves time by
  `D`; attached after two support children of a binary root, with singleton groups, it keeps the
  edge count bounded while the span grows without bound. **Formalized: the repaired lemma.** The
  edge estimate (12) holds for arbitrary zero-potential unary links
  (`UND.Contour.GroupedSystem.grouped_terminal_estimate`, `grouped_terminal_estimate_paper`: unary
  links only need `ψ_c(un θ) = ψ_c(θ)`, no time condition); the span bound is claimed only when
  unary links also preserve time (`witness_span`, hypothesis `hun : ∀ θ, UN θ → time (un θ) =
  time θ`); the two-terminal assertion (`singleton_two_le`) requires a binary root (`S.NF ρ`), so
  every arm of the root source starts with a positive support edge. Per the audit, every
  application in the paper has valid clocks (raw and deep-query contours; memory uses the edge
  estimate only; rare-birth contours have same-time groups). `Statements.lean` is unaffected
  (Theorem A does not mention Lemma 5.1).

* **FD2 §3.2, the phase-zero gate classification** (QB, session 3). **Printed in v1.0.0;
  corrected in v1.1.0** (the formal target matches v1.1.0). As
  printed, "so the phase-zero gates are exactly the finite bottom rows with `d ≥ k`" is false as a
  global statement about all gates; it is correct for gates on finite bottom rows. **Formalized: the
  restricted form** `UND.Chart.lanePhase_bot_eq_zero_iff`: for the lower endpoint `Bot_d(m) =
  frameLo (phaseOffsets t) d m` of a depth-`d` row frame, `lanePhase t k (Bot_d(m)) = 0 ⟺ k ≤ d`
  (with `lanePhase_bot`, the printed congruence `p(Bot_d) ≡ (4m+1)4^d (mod 4^{min(d+1,k)})`, exact).
  Every later use (Prop 4.3: "both critical depths are gated since `a - 1 ≥ k`"; Section 6) is about
  gates on finite bottom rows of explicit depth. **CONFIRMED (QB, s4).** Tile-level forms (s4):
  `UND.Chart.end_gate` and `UND.Chart.IsRChart.gate_iff`.
* **Note (not a deviation), Prop 2.1:** the printed count `B(n_A + n_Q) + (B + 1)` counts the helper
  site `w - e_x + v` twice (it is the `j = 0` member of the `B` sites `w + j e_y - e_x + v`); the
  formal neighbourhood has `B` helper sites and the printed bound `≤ B(n_A + n_Q + 2)` holds.
  **ACCEPTED (QB, s4)** as a printed miscount. **Printed in v1.0.0; corrected in v1.1.0.**

## Decisions made in session 1 (details in `BLUEPRINT.md`, Part D)

D1 statement of record as `def … : Prop`, theorems in `Main.lean` (**confirmed by QB, s2**); D2
reuse by olean import on `LEAN_PATH`, no lake; D3 one generic port of FNE's Section 2 layer; D4
chart alphabet as a finite type with matching relations; D5 `Fin 6 → ℤ`; D6 alphabet `Fin |Σ|`;
D7 lane-phase decoder from UPD's `qphase_local`; D8 `k`, `n₀` by `Nat.find` (both done); D9
windows for every `n₀`; D10 pullback rendering (**accepted**); D11 "computably specified" not
rendered (**accepted**, F9).

## Decisions made in session 2

* **D12 Memory between initial laws.** The forgetting core's `HasMemory` compares two point
  masses; Theorem 7.3 compares two translation-invariant initial laws (the bit-0 and bit-1
  initializations). `HasMemoryFrom ε μ μ'` takes two initial laws; `hasTwoTIStationaryLaws_of_memory`
  is exactly the last paragraph of the proof of Theorem 7.3 (Cesàro limits along a common
  subsequence are stationary, translation invariant, and differ on the witnessing cylinder).
* **D13 Kernel discipline for huge closed constants** (extends QB's kernel ruling). Lean's kernel
  unfolds abbreviation heads (`HMul.hMul`, `HAdd.hAdd`, …) before regular definitions and then
  evaluates `Nat.mul`/`Nat.add`/`Nat.succ` by `whnf` of their arguments; for a definition whose
  body contains `kParam` (a `Nat.find`), `B = 4^k`, `N₀` or `K_rare`, even its `rfl` equation lemma
  (used by `unfold`) makes the kernel run out of memory. Hence: every such quantity is a function
  of its parameters (`DeltaRareOf B`, `KrareOf B`, `epsStarOf B N`), every lemma about it is
  proved for variables, and the closed constants (`Krare := KrareOf Bparam`,
  `epsStar := epsStarOf Bparam N0`) are used only through one-step instances (`Krare_pos :=
  KrareOf_pos Bparam`) or `rw [Krare_eq]` with `Krare_eq : Krare = KrareOf Bparam := rfl`; never
  `unfold Krare` or `positivity`/`omega` on closed terms containing these constants.
  `Bparam`, `N0` are also `@[irreducible]` (elaborator side).
* **D14 Lemma 5.1, abstract form** (`Contour/Grouped.lean`, ADAPTED from FNE's contour lemma):
  - acyclicity is a rank `rk` strictly decreasing along every edge (support and unary), not a
    time decreasing by exactly one (unary characteristic links of Lemma 7.2 change physical time;
    virtual levels of Lemma 5.4 are bookkeeping levels);
  - the good support of each charge is one of the two selected supports (`good : C → V → Bool`),
    as in the paper's two-cluster supports ("for each charge it provides a good parent");
  - potentials are inequalities: good gains `≥ ϱ₊`, all gains `≥ -ϱ₋`, unary links `0`; sum zero;
  - the group-oscillation hypothesis is rendered as: for any terminal leaves `φ c`, `φ' c` (one per
    charge) of one group, `Σ_c (ψ_c(φ c) - ψ_c(φ' c)) ≤ Ω` — the sum of the five oscillations is
    exactly the supremum of this quantity; groups at unequal times are allowed;
  - "`g` distinct groups and a connected copied-arm witness containing the root": a finite set `P`
    of sources (poles), containing the root source, linked to it through shared groups, whose
    `c`-arms end in `|P|` distinct groups, the same for every charge; `e` = binary arm edges
    counted with multiplicity; the witness is `armEdges P ∪ grpEdges P` (all identification links
    between arm ends in one group), `ConnectedAt` the root. **[choice]** The paper's counts of
    group star edges (Lemma 8.4: `≤ 5g`) are left to the instance (a star sub-witness can be
    extracted there);
  - span: see the fidelity deviation **FD1** below (the printed sentence is false; the repaired
    form is formalized).
* **D15 Lemma 8.5 hypothesis.** "Complete common-noise trajectories are almost surely unique" is
  rendered as: almost surely, any two complete trajectories have the same state at time 0
  (`∀ᵐ ω, ∀ X Y, IsComplete ω X → IsComplete ω Y → X 0 = Y 0`), which Lemma 8.4's "full-state
  equality" gives. The attraction part goes through `forgets_of_coupling` (window TV distance ≤
  coupling-failure probability) rather than coupling with a stationary start; same content.
* **D16 Coupling-failure events.** The event "some two starts differ on `O` at time `t`"
  quantifies over all configurations; it is shown measurable through the finite dependence cone
  (`measurableSet_disagree`), which is what "determined by a finite noise cone" means.

## Decisions made in session 3

* **D17 Lemma 9.1 as a union bound over literal encodings.** An encoding is `(K, A)`: a set `K` of
  at most `N` graph edges connected at the root and a marked subset `A` of its vertices (or the
  root); `|encLe N| ≤ 2Σ_{e≤N}(2Δ²)^e ≤ 4(2Δ²)^N` (FNE's `card_le_pow` for the traversal; the
  vertex bound `|K| + 1` gives `2^{e+1}` subsets). The constant enters through a hypothesis
  `∀ g ≥ 1, 4(2Δ²)^{cg} ≤ K^g` (instances `K_mem`, `c = 256`; `K_rare`, `c = 512`), so the
  probabilistic sum `measure_le_tsum_groups` is generic. The projection of Lemma 7.2 is
  `Finset.image (Sym2.map f)` followed by dropping loops (collapsed group links); both keep
  connectivity. The "two unary links per positive support edge" of Lemma 7.2 is used with the
  corridor merged into one zero-potential unary link (`pLen_le_two_pBin` under "no unary link is
  followed by another"); merging only lowers the edge count.
* **D18 The rule, generic in the chart tile set.** `WangRel τ` (two matching relations), live
  letters = legal `3×3` block × bit, `ChartSym = Option LiveLetter` (`none` = `⊥`); `ChartData B τ`
  adds the tile functions `orig`, `endP`, `hrow : τ → Bool` and `phase : τ → ZMod B`, read on the
  central tile of a live letter. Providers are indexed by `Prov = Option (Fin 4) × (Fin 4 → Fin 16)`
  (`|Prov| = q`); `F_R` counts checked providers over this index type (the five clusters are
  disjoint, so this is the count over sites). The threshold letter is `Classical.choose`, unique by
  `2h > q`.
* **D19 Helper alphabet** `Fin 100`: `0` LOW (`{0}`), `1` UNKNOWN (`{0,1}`), `2 … 99` HIGH (`{1}`);
  representatives `0, 1, 2`; intervals as the three-element type `Ival`.
* **D20 Automaton.** `siteEquiv`: coordinates `0, 1` planar, `2 … 5` provider. `caOf G N`: the local
  rule evaluates `G` at the origin on the pattern extended arbitrarily off `N`; `caOf_apply` shows
  the global map is `G` (translation commutation + locality). Locality of (6) needs `B ≥ 1` (the
  base `w` is the `j = 0` base). `ruleCA CD s` is the automaton for any chart data; the concrete
  `R` (S7) and `B = Bparam`, `s = sParam` are plugged in at the end (D13).
* **D21 Elaborator discipline for `T` and concrete finsets.** In `Rule/Proposal.lean`, `UND.Param.T`
  is locally irreducible: otherwise unification unfolds `F_R^[500]` (or the box `[-500, 500]²`) and
  hits the recursion limit; the concrete neighbourhood finsets `nbhdA`, `nbhdQ`, `cubeQ`, `nbhdP`
  are `@[irreducible]` and opened by `unfold` only.
* **D22 Assembly hook.** `Branches U A` (memory between two TI initial laws when `U(n)` does not
  halt; a.s. unique complete trajectories at time 0 when it halts) is the premise of
  `theoremA_of_branches`, a theorem, not a named hypothesis; the two branches are Theorem 7.3 and
  Lemma 8.4.
* **D23 Walls in every phase.** `walls_VW_of_rank`/`walls_HW_of_rank` replace UPD's `NotInt`
  (all ranks finite) by a finite parent rank of the one coordinate, exactly the form Lemma 3.3
  applies inside one closed frame.

## Decisions made in session 4

* **D24 The routing alphabet generic in the content alphabet.** `Chart/Routing.lean` defines `R`
  for any finite content alphabet `S` with `ContentOps S` (`init`, `f_P`, the HALT mark, the
  read-only tracks `h_in`, `π`); `Chart/TheCA.lean` plugs in the machine `P`
  (`contentP U n0`). The chart data has `B = 4^k` literally (`ChartData (4^k) (RTile C k)`), so
  `theCA U = theCAOf U n0Param kParam sParam` runs the rule with `4^kParam` lanes. `Bparam` is
  `4^kParam` by an `@[irreducible]` definition; no equation `Bparam = 4^kParam` is stated yet
  (its kernel check must follow D13: the kernel may unfold `HPow.hPow` before `Bparam` and
  evaluate `kParam`). Later lemmas should be stated for `B = 4^k` with `k` a variable and
  instantiated at `kParam` in one step, or the equation added with a kernel-safe proof.
* **D25 The phase extension carries the central word.** A tile of `R` is an allowed routing tuple
  together with its central word of radius `ρ_{2k}` (D7; the higher-block presentation), whose
  centre is the tuple's quarter; tiles match when routing colours match, words overlap
  consistently, and the decoded phase `phaseTable k` copies horizontally and increases by one
  vertically (the printed "require `p` to agree with that table, to copy horizontally and increase
  by one vertically"). The controller's `p` is `phaseTable k` of the word. In every legal chart the
  words are the true words (`IsRChart.word_apply`), hence `p` is (9) in every phase
  (`IsRChart.phase_eq`).
* **D26 Decorated quarters as Wang colours.** `DQuarter.colE … colS` follow the quarter colours of
  the hard-model core, with `V` on north/south and `H_row` on east/west external colours; the
  matching relations are colour equalities (as printed: "a finite Wang construction").
  "Every finite cutoff occurs over every typical scaffold chart" is formalized for charts whose two
  phase coordinates are not integers (`NotInt`, every parent rank finite), which contains the
  Haar-typical phases.
* **D27 Lemma 3.3 as building blocks.** The board statement is proved as lemmas on one depth-`d`
  board (`board_row`, `board_col`, `board_active`, `board_not_vcarrier`, `board_not_hcarrier`,
  `board_flags_row/col`, `board_record`, `board_init`, `board_step`, `board_vlink`,
  `board_bottom`, `board_top`), with "consecutive free coordinates" in place of the indices
  `x_0 < … < x_{N_d-1}` (the first and last are `L_* + 1`, `R_* - 1`). An indexed packaging
  (`allphase_board`) will be added when Lemma 4.1/Prop 4.3 consume it.
* **D28 Machine `P` rendering choices** (M1, `Machine/P.lean`) **[choice, for QB]**: "returns with
  continuation `Z`" from a non-SETEND state is a stay move into `RET_Z` (SETEND moves left into
  `RET_{R_00}`, as printed); `RUN_q` at a halting `q` enters HALT with a stay move; a halting
  successor of `U` moves as `U` does and enters HALT (a move off cell `0` then fails, matching
  `UPD.Machine.step = none`); a failing head at a tape end keeps the written symbol; `n_*` and the
  tracks are as printed. These affect only Lemma 4.1's step counts, not its statement.

## Decisions made in session 5

* **D29 Lemma 4.1(b) in the form Prop 4.3 consumes.** Lemma 4.2 forces `j_* + 2 = 2^{a+1}` on
  every large board, so the clause "any other positive count eventually fails" is not used by
  Theorem A and is not formalized. Formalized: `decode_halts` (`j_* + 2 = 2^e`, `e ≥ n₀ + 2`,
  parity bit one, `U` halts on `e - n₀ - 1` ⇒ HALT at one time `T`), `decode_no_halt` (`U` does not
  halt ⇒ never HALT), `guard_no_halt` (first zero with parity bit zero, or no zero ⇒ never HALT).
  The machine is analysed on the unbounded tape (`stepU`); the board's bounded run agrees with it
  until an exit (`stepB_iterate`, `stepB_iterate_eq`), and a head is at most at cell `i` at time `i`,
  so `N_d > T` suffices (`runP_halts`). **[for QB]**: confirm that omitting the non-power clause is
  acceptable (it is a statement about `P` only; no later lemma uses it).
* **D30 Uniformity over the input tracks by forgetting.** Away from SCAN, `δ_P` neither reads nor
  writes `h_in`, `π` (`program_forget`), so the run commutes with erasing them (`iterate_forget`).
  After SCAN the run is one fixed trajectory, which gives one halting time `T` for every board of
  every depth `d > a` (the rows above the initial zero differ between boards). Step counts are
  never computed: phases are composed by reachability (`Reaches`).
* **D31 Typicality for Prop 4.3 (QB s5, D26 follow-up).** The hard-model core's construction of
  routing tags (`UPD.BG.cfg_legal`, `Background/Construct.lean`) assumes `UPD.Scaffold.Typical τ`
  (resolving, both phase coordinates not integers, every coordinate in a finite frame: `Digit2`),
  which is Haar-full (`UPD.Scaffold.ae_typical`) and implies `NotInt` of both coordinates. So the
  nonhalting branch of Prop 4.3 will use `Typical` (stronger than D26's `NotInt`, still the
  Haar-typical set); `cutoff_exists` (stated under `NotInt`) applies to it. The halting branch
  (`chart_wrong_flag`) needs no typicality: it holds in every phase. Section 7's "almost every
  phase" statements will be taken over `Typical` (full measure), as in the hard-model core.

## Decisions made in session 6

* **D32 The translation-invariant chart law as an equivariant push-forward** (Prop 4.3). The paper
  takes a weak limit of spatial averages of one chart. Formalized instead: the image of Haar measure
  under `τ ↦ chartOf τ` (`chartLaw`), the template of the hard-model core's `PhaseSystem.isTILaw`.
  It is translation invariant because the chart of `τ + a` is the translate of the chart of `τ`
  (`chartOf_shift`, proved directly field by field: no uniqueness theorem for `R`-charts is needed)
  and Haar measure is invariant under `τ ↦ τ + a`; its phase is Haar and typical almost surely by
  construction, and it retains the cutoff (`ae_goodChart`). Same conclusion as printed ("a spatially
  translation-invariant law of legal charts … with row flag one on finite bottom depths `d < a` and
  zero on depths `d ≥ a`": `chart_law_exists`, `chartOf_bottom_flag`). The global bit is added by
  the live-letter lift in Section 7.
* **D33 Lemma 5.3 for flagged trajectories and closed marked sets.** The lemma is proved for any
  `ℤ`-indexed trajectory on `ℤ² × ℤ⁴` whose unflagged symbols are the proposal of the previous
  configuration (`IsFlagTraj`) and any marked set containing the flags and closed under the
  two-cluster rule (`MClosed`); the raw marked set `𝓜` (`marked`, the increasing limit of
  `𝓜^{t₀}`, `markedFrom`) is such a set (`marked_closed`), and every complete trajectory of the
  automaton decodes to a flagged trajectory (`isFlagTraj_of_complete`, `coherence_complete`). The
  printed "using `𝓜^{t₀}` … send `t₀ → -∞`" is absorbed: the induction runs on the limit `𝓜`,
  which already satisfies the closure property.
* **D34 The routing fields of the construction are the hard-model core's.** `rawVal` takes `o^W …
  e^N` verbatim from `UPD.BG.cfg U τ (fun _ => +)` (`oEc`, `oNc`, `eEc`, `eNc`); our (O1)–(E3),
  carriers, activity and flags are definitionally those of `UPD.SiteVal`, so `UPD.BG.cfg_O1 …
  cfg_E3`, `cfg_active`, `cfg_grids_c`, `hseg_carrier`, `vseg_carrier` apply unchanged (DMhard
  Props 5.1, 5.7, Lemma 5.3, proved in the hard-model core). Channels carry the row frame
  (`HSegM` etc.), because the board's input tracks depend on it. The chart is a total function
  of `τ` with a fallback tile (`toTile`), never used for typical `τ` (`chartOf_val`).

## Decisions made in session 7

* **D35 Lemma 5.2 as formalized** (`Contour/RawPaths.lean`). "Backward ordinary dependency path":
  a sequence `(p k, t - k)` with `p (k+1) = (p k).1 + μ, (p k).2 + s_π` for `μ ∈ Mo`, `π` a
  provider (`OrdStep`, the data checker's dependency of `A_t`); Lemma 8.3's "live data centre
  parents" are the case `μ = 0`. The marked derivation of `𝓜^{t₀}` is the `GroupedSystem` `sys E t₀`
  on space-time points (rank `t - t₀`, parents chosen by `Classical.epsilon` among the two-cluster
  witnesses of `markedFrom`, charge `c` good = cluster `≠ c`, singleton groups), so Lemma 5.1 is
  applied verbatim (`grouped_terminal_estimate`, `hosc_singleton`, `witness_span`): a contour has
  `85e ≤ 4000(f-1)` (so `e ≤ 48(f - 1) ≤ 50(f-1)`), flags in `[t - e, t]`, and its non-loop
  witness edges (at most `e`: no unary links) are ordinary steps. The path argument restarts at
  index `k + e + 1` (one step below the slab, whatever the actual earliest flag), so slabs are
  disjoint by construction; coverage `e + 1 ≤ 50f`, edges `2e + 1 ≤ 101f`. The union bound is
  `measure_le_tsum_from` (Lemma 9.1's `measure_le_tsum_groups` restricted to `g ≥ G`), with
  `Δ = 18q`, `c = 256` (`101f ≤ 256f`), `K_mem`; the tail `Σ_{j}(K_mem ε)^{j+G} → 0`
  (`ENNReal.tendsto_sum_nat_add`). Stated for every `ε ∈ [0, 1]` with `K_mem ε < 1`
  (`raw_paths`), and at Section 9's threshold `0 ≤ ε ≤ ε_*` (`raw_paths_threshold`, through
  `epsStar_le_mem`, `raw_base_lt`). No measurability of the path event is needed (outer measure).
* **D36 Lemma 5.4 as formalized** (`Contour/Deep.lean`). A vertex is `(y, j)`: `j = 0` an actual
  space-time point, `j ≥ 1` the virtual value `F_R^j(D_s)(y.1)` placed at the bookkeeping time
  `y.2 = s + j`; then the printed characteristic potentials (`χ = P + v(s + j)`) are the raw
  potentials of the bookkeeping point and every support (virtual: a wrong centre provider; final:
  wrong actual data; actual: the marked derivation) is a `par` step, so Lemma 5.2's gains apply.
  "Relative to the chart in Lemma 5.3" is the hypothesis `hc` (the chart agrees with every
  unmarked live reading, the conclusion of `coherent_chart`), which makes every wrong live actual
  reading at time `t - 1` marked (`Ctx.Good`). Ranks: derivation depth (`Nat.find`) on actual
  points, `1 + max` of the supports on virtual levels. Every root arm crosses all `T` levels
  (`gBin_add_level`), so `T ≤ e`; with `85e ≤ 4000(f-1)` this gives `f ≥ 12 ≥ 11`, and
  `e ≤ 48(f-1) ≤ 50(f-1)`. Flags are no later than the queried input time `t - 1` and no earlier
  than `t - 1 + T - e ≥ t - e`; the lag form is `deep_wrong_lag`. The contour's edges live in the
  deep graph `nbrD` (both directions, levels `j → j - 1` and `0 → 0`, Moore and provider offsets;
  degree `≤ 36q`), ready for Lemma 8.2's encoding.

* **D37 Lemma 6.2's probabilistic core, abstract** (`Sensors/Tails.lean`). The tails are proved for
  any finite family of independent `{0,1}`-valued random variables (the lane indicators of a gate,
  independent by Lemma 6.1): the short tail by Chernoff at `t = log(θ/p_r)` with `θ = .75C`,
  `p_r = .53C4^{-r}` and the printed exponent bound `.03C + rC/3` (`log(75/53) ≥ 11/32` is proved
  from a degree-five Taylor bound of `exp` rather than from `log x ≥ 2(x-1)/(x+1)`; same
  inequality), the long tail by Mathlib's Hoeffding inequality for sub-Gaussian variables (centred
  indicators are `1/4`-sub-Gaussian), and `e^{-x} ≤ 2^{-⌊x⌋}`; the union over a bin is
  `eta_bound`, with the counts (at most `3·4^r` short ends of offset `r`, at most `2` long ends)
  as hypotheses: they are chart geometry (N2). The bases are related to `UND.Param.uB`, `zB`,
  `wB`, `etaHat` by the `*_cast` lemmas (D13: no closed constant is evaluated).
* **D38 The ideal experiments** (`Sensors/Ideal.lean`). The ideal field along a ride copies and is
  reset at the origin, so its value at the end is the most recent replacement mark among the ride's
  atoms (or the reset value); `RideEv g L` is that event for a mark predicate `g` and distinct
  atoms `L` (most recent first), and `rideEv_real` computes `ρ(1 - (1-ε)^{|L|})` by induction,
  using `infinitePi_inter_eq_mul` (independence of events determined by disjoint finite coordinate
  sets, from `iIndepFun_infinitePi` and `iIndepFun.indepFun_finset`). For the automaton's noise
  the upper and lower marks of lane `j` have probabilities `99/100` and `98/100` (from
  `uniformLaw_field`), which gives (14) and (15) (`upper_law`, `lower_law`). Which atoms a ride
  reads (the `ℓ_d` atoms of the true ride, the recent `W`) is Lemma 6.1's geometry (N2).

## Decisions made in session 8

* **D39 Lemma 6.1 as formalized** (`Sensors/Ownership.lean`). The characteristic (16) of a point is
  `(c, y, Q) = (x - t, y, P + vt)`; `chSite c y Q t` is its point at time `t`, `laneAtom c y Q j t`
  the noise atom of the output at time `t` on the lane characteristic `(c, y + j, Q)` (two-sided
  index `(t, w)` = the replacement of the output at time `t`, as in `flagsOf`). The true ride of
  lane `j` of the gate ending at proposal time `t` is the list of its `n` most recent atoms (times
  `t - 1, …, t - n`; `n = ℓ_d` from the origin output, `n = W` for the recent window). A finite
  phase-zero gate (`IsGate tc tr k d c y t`) is stated on the two phase digit sequences: the row
  is `Bot_d` of a depth-`d` row frame with `d ≥ k`, the end `c + t` is `R_d`; `isGate_of_end`
  connects it to the chart's `End` with lane phase zero (`end_gate`). **`ownership`**: an atom lies
  on the ride of at most one (gate, lane, step `< ℓ_d`) (block partition of the rows,
  `phaseZero_block`; depth determined by the row; depth-`d` ends `4^{d+1} > ℓ_d` apart).
  Independence on disjoint coordinate sets is proved once (`infinitePi_biInter_eq_prod`,
  `iIndepFun_of_detBy`); events determined by finitely many coordinates of the finite alphabet are
  measurable (`measurableSet_of_detBy`).
* **D40 Lemmas 6.2, 6.3 as formalized** (`Sensors/Gate.lean`, `Joint.lean`, `Selected.lean`). The
  intrinsic bad events are `ShortBad` (`≥ s` lanes with an upper success along `ℓ_d` atoms) and
  `LongBad` (`< s` lanes with a lower success along the recent `W` atoms); `GateBad` switches at
  the critical depth `a` (flags one below `a`, zero from `a`, as in the cutoff chart). The source
  label is `((c, y, Q), i_bin)`; `RawEv` = some flag among the `W` outputs of the bin on the
  characteristic (`RideEv` with the trivial mark, `≤ εW ≤ C`); `StatEv` = some finite phase-zero
  gate ending in the bin has its bad event (empty off gate rows). Per bin at most `4^r` short ends
  (`r = a - 1 - d`) and one long end (`card_ends_le`; printed `3·4^r` and two). The statistical
  support is the `B` lane characteristics in the bin and its predecessor (`statSupp`); supports in
  one residue class mod 3 are disjoint (`statSupp_disjoint`). The abstract `joint_bound` expands
  `⋂(R ∪ S)` over the raw selection `A ⊆ G`, multiplies the raw part (`≤ C^{|A|}`), bounds the
  statistical part by its largest residue class (`≤ η^{|G∖A|/3}`), and uses
  `P(X ∩ Y) ≤ min(P X, P Y) ≤ √(P X · P Y)` (the printed Cauchy–Schwarz step); the sum is
  `(√C + η^{1/6})^{|G|}`. The parameter facts are the structure `Regime`, supplied on every window
  by `regime_final` (with `B = 4^k`: `Bparam_eq` is kernel-safe because the kernel unfolds
  `Bparam` before `HPow.hPow`; D24 resolved). `joint_source_final` is Lemma 6.3 with
  `γ = gammaOf (4^k)`, the base of `mem_series_lt`.
* **D41 Lemma 7.2, combinatorial core** (`Memory/Count.lean`) **[for QB]**. The group links of the
  copied-arm witness (`grpEdges`: all links between arm ends of one group) are counted linearly:
  since the arms of each charge end in distinct groups, a group receives at most one arm end per
  charge, so there are at most `|C|²|P| = 25g` links (`grpEdges_card_le_lin`). With Lemma 5.1 at
  zero group oscillation (leaves of one source label have equal characteristic potentials) and at
  most two unary links in a row (`pLen_le_three_pBin`), the witness has at most
  `3·(4000/85)(g-1) + 25g < 167g` edges, and `≤ 169g < 256g` after at most two unary links in front
  of the root (`prepend`). The printed count uses a star sub-witness (`5g` source-role links,
  total `< 149g`); the linear clique count stays inside the same `256g` budget, so no star
  sub-witness is needed for Lemma 7.2. The same count gives Lemma 8.4 `2·130g + 25g + g < 512g`.
  **Proposed:** this settles D14(b) (Lemma 8.4 included); QB to confirm.
  `mem_encoding` produces, at every root, a literal encoding with `g ≥ 1` distinct labels, each the
  projection of a terminal leaf reached from the root, given a projection `f` whose system steps
  and same-group links lie in a symmetric graph; `mem_union` is the union bound
  `μ(Ev) ≤ Σ_{g≥1}(K_mem γ)^g` against any joint source law `γ^{|G|}`.
* **D42 The helper ride** (`Memory/Ride.lean`). `HelperTraj s Y ω`: the helper fields follow (4)
  off flags and are the replacement mark at flags, at every integer time; the complete
  trajectories (Section 8) and the stationary helper initialization (Section 7: data held at the
  chart for `t ≤ 0`, helpers following (4) with perfect drivers) both satisfy it. With live
  drivers along the first `n` ride bases (no origin), the end input interval is the most recent
  mark along the `n` atoms, else the older interval (`ride_copy`); with the origin at the next base
  it is the ideal upper experiment (`ride_short`). At a correct short gate `h_w` is exactly the
  number of upper successes (`hcount_short`: an erasure is `ShortBad`); at a correct long gate
  `l_w` dominates the lower successes (`lcount_long`: absent `LongBad`, no erasure). All lanes read
  the same driver bases (`gate_J`).

## Decisions made in session 9

* **D43 Lemma 7.1 as formalized** (`Memory/Derivation.lean`). Vertices `(y, j) : Pt × ℕ` as in
  Lemma 5.4: level `0` is the data `D_t(w)`, level `j ≥ 1` the virtual value `F_R^j(D_{t-j})(w)` at
  bookkeeping time `t`; the ordinary driver `A_t(w)` is the level-`1` vertex `((w, t), 1)`, the deep
  driver `Q_t(w)` the level-`T` vertex `((w - (T-1)v, t - 1 + T), T)`. Bad = `≠ some (ref u)`.
  Binary: a bad virtual value (`NFv`), or bad unflagged data with a bad ordinary driver (`NFd`,
  supports = those of `A_t`); both have two bad supports in distinct clusters (`exists_pgood`:
  `F_R(D)(u, P) ≠ ref u` leaves more than `K` failed checks, each with a bad Moore input by
  `chk_chart`). Unary (`UNd`): bad unflagged data with a correct `A_t` and a bad driver node
  (`Link`): its own `Q_t`, or `A`/`Q` at a ride base `i + 1 ≤ W` updates back on the base
  characteristic; every link target is binary (`hUUU_sysM`). Rank `(T+1)·(t - j) + j`. Potentials:
  the raw potentials, functions of `χ = P + vt` (`psi_eq_chi`); links keep `χ`. The group of a
  vertex is its projection `fM` (characteristic `(x - t_out, y, χ)`, bin `⌊t_out/W⌋`, level), so
  terminal leaves of one group project to one point and `hgl` is vacuous; the projected graph
  `nbrM` has degree `≤ 108q + 6 ≤ Δ` (support steps `±(μ_x + [j ≤ 1], μ_y, s_π - v)` with bin step
  `0`/`1` and level `j - 1`; links to level `1` or `T` with bin step `0`/`1`). The sources are the
  labels at level `0` (`RM`, `SM` empty elsewhere). `term_source` is the printed case analysis:
  flag → raw; correct `A`, `Q` and erasure → the chart's gate (`Hyp.gate`); all ride drivers correct
  → `hcount_short` (short: `s ≤ h_w` is `ShortBad` over `ℓ_d` atoms) or `lcount_long` (long:
  `l_w < s` forces `LongBad` over `W` atoms).
* **D44 The reference chart** (`Memory/RefChart.lean`). The bit-`b` lift of an `R`-chart is
  `u ↦ (3×3 block at u, b)` (`liftChart`, a full legal chart); as a total function of the chart it is
  `liftSym` (`⊥` where the block is not legal, never for legal charts). `chart_gate` supplies
  `Hyp.gate` from `IsRChart.gate_iff`, `chartOf_bottom_flag`, `orig_iff`, `depth_unique` and
  `leftEnd_back`.
* **D45 Mem1 as formalized** (`Memory/Init.lean`, `Memory/InitLaw.lean`). The ideal field `j` at
  `(t, w)` is `firstHit` along the copy chain `w - m(e_x - v)` at times `t - m` (a hit: a flag, or an
  origin of the chart at the base `w - j e_y`); `initField_rec` is rule (4) with the chart's drivers.
  `hyb` is the hybrid trajectory (D42); `X0` its time-0 state as a function of the negative-time
  noise. Measurability (`measurable_X0`) via `measurableSet_firstHit` (first hits on sequences of a
  countable discrete space) and the measurability of the chart symbols. The two-sided noise is the
  glue of independent negative- and positive-time copies (`glue_law`). `law_initLaw`: the law at
  time `t` is the push-forward of `P ⊗ noise₂` along the automaton run from `X0`.
* **D46 Theorem 7.3 as formalized** (`Memory/Theorem.lean`). Chart parameter: the Haar phase, the
  chart `chartOf … τ t0` of the nonhalting cutoff `2a - 2` (`t0` from one typical phase, as in
  `chart_law_exists`). The data error at the origin has probability `≤ S < 1/4` for every typical
  phase (`mem_bad_le` with `hyp_typical`), integrated by Fubini (`law_initLaw_le`). Memory on the
  one-site cylinder "live data with bit `1`" at the origin: `≥ 1 - S` from bit 1, `≤ S` from bit 0,
  `α = 1/2` (`memory_branch`). Only data errors are bounded (the second coordinate is not needed by
  the conclusion).
* **Lessons (s9).** (a) `rw`/`simp` unify at reducible transparency: a noise of type
  `(ruleCA CD s).Noise₂` does not match a pattern over `PNoise CD` (both are
  `ℤ × Site 6 → Bool × Fin |Σ|`, defeq only by unfolding `ruleCA`); keep each proof in one world
  (`glue_law`, `law_initLaw` are stated on `(ruleCA CD s).noiseLaw₂`), state lemmas that meet both
  worlds generically (`law_initLaw_le`), and transport with `congrArg (· ∈ Z) h |>.mpr` instead of
  `rw`. (b) `scripts/audit.sh` greps `AXIOMS.txt` for `error`: never put `error` in a theorem name
  (`mem_error_le` was renamed `mem_bad_le`). (c) Concrete finsets of the projected graph
  (`idxS`, `idxB`, `nbrM`) must be `@[irreducible]` (D21), or membership proofs hit the recursion
  limit. (d) `Measure.eq_infinitePi` needs the factor instance passed by name
  (`(hμ := fun _ => hm)`). (e) `Int.ediv_mul_add_emod` (not `ediv_add_emod`),
  `Equiv.eq_symm_apply` (not `apply_eq_iff_eq_symm_apply`), `measurable_pi_iff.mpr` (not
  `measurable_pi_lambda`).
* **Source note (s9).** During session 9 the release folder moved to version 1.1.0 (commit
  `ad1d39d`, DOI 10.5281/zenodo.24152233; "Theorem A, Theorem 9.3, Corollary 9.4 and the
  construction constants keep their statements and values"; Theorem 7.3's proof now bounds the
  error by `e_base < 3/125`). The formalization follows v1.0.0 (`git show f2559d3:paper/main.tex`);
  Theorem 7.3's statement is the same in both. **For QB:** confirm that Section 8 is to be read
  from v1.0.0 (v1.1.0 lists correction (iv), "the birth-contour clock in Lemma 8.4 is stated once").

## Decisions made in session 10

* **D47 Lemma 8.1 as formalized** (`Forget/Miss.lean`, F24). Inclusion of represented intervals
  `isub` (`{0} ⊆ {0}, {0,1}`; `{1} ⊆ {1}, {0,1}`; `{0,1} ⊆ {0,1}`); a base is *monotone* (`GoodAt`)
  when `A = ⊥` (UNKNOWN), or `A` is live and `Q = ⊥` (union with `{0}`) or `Q` is live with the chart's
  origin status. Along monotone bases the ideal value (the most recent mark, or the reset `{0}` at
  the true origin) lies in the actual interval (`ride_mono`, `ride_mono_short`): at a short wrong
  flag `0`, `l_w ≤` upper successes, so `l_w ≥ s` is the short bad event; at a long wrong flag `1`,
  lower successes `≤ h_w`, so `h_w < s` is the long bad event. A non-monotone base is a live wrong
  deep query at a lag `ℓ ≤ W` (`missed_erasure`).
* **D48 Lemma 8.2's probabilistic core** (`Forget/History.lean`, F23): see F23; the event of a
  witness is (validity) ∩ (intrinsic events of its intrinsic steps) ∩ (its flags); the intrinsic
  events of distinct nodes are determined by disjoint atoms (`atomsK_disjoint`: the characteristic
  `x - t` differs), the flags of distinct deep blocks lie in disjoint time slabs (`card_flagSet`).
* **D49 Lemma 8.2 as formalized** (`Forget/Eliminate.lean`). Generic in the chart data, with the
  chart entering through a *gate oracle* (`GateOracle`: every full legal chart has a gate of the two
  critical kinds), supplied for the automaton by Prop 4.3 (`halting_gate`). From an unmarked live
  reading: the coherent chart (Lemma 5.3), its wrong critical gate, an unmarked live reading at the
  gate site (`coh_cover`), unmarked live *data* parents at the same planar site forever
  (`uld_back`), and at each vertex Lemma 8.1 + Lemma 5.4 (`node_prop`): a historical path
  (`hpath_of_ul`), excluded almost surely (`no_ul_generic`, countable union over the gate site, the
  kind and the root node).
* **D50 Lemma 8.4 via the raw set** (`Forget/Coupling.lean`, F21, F22). An unflagged discrepancy has
  a discrepant parent in `N_F` (`proposal_local`) and a live `A_t(w - j e_y)`, `j < B`, in one run
  (otherwise both proposals are `(⊥, ⊥, UNKNOWN^B)`, `proposal_of_dead`); a live `A_t` is in `𝓜`
  (`live_marked`, from Lemma 8.2); flagged outputs are common (`flagged_complete`). The infinite
  discrepancy path is excluded by Lemma 5.2's contours with anchors and connectors
  (`exists_cover_C`, `discEv_null`), simultaneously at every root.
* **D51 The halting branch** (`Forget/Halting.lean`). Proved for `theCAOf U n₀ k s` with variable
  parameters (`halting_branch_gen`, s9 generic-bridging pattern; D13) and instantiated once
  (`halting_branch`). The single-gate bounds (`gate_bounds_final`: `≤ u_B` short at depth `a - 1`,
  `≤ w_B` long, both `≤ η̂_B`) are stated for any chart data with `B = 4^k` lanes, as
  `joint_source_final`. Kernel discipline: the rare base is proved for variables (`rare_of`) and
  instantiated at `KrareOf Bparam`, `N₀`, `ε_*` before rewriting `Bparam = 4^k` (a direct proof
  exhausted kernel memory).
* **D52 Main.** `theorem_A := UND.Memory.theoremA_of_halting UND.Forget.halting_branch`; the audit
  of the three final targets is now strict.

## Open risks

1. None for the core: the sorry census is 0 and the three final theorems use only the three allowed
   axioms (`AXIOMS.txt`, AUDIT OK).
2. For QB: F21 (Lemma 8.4 through `𝓜` instead of the rare-birth field), F22 (Lemma 8.3 not
   formalized, unused), F23 (Lemma 8.2's packing indexed by blocks) are proof-route differences;
   the statements of Theorem A, Theorem 9.3 and Corollary 9.4 are unchanged.
3. Release: done in session 11 (comparator, leanchecker, nanoda, axioms, statement eye-read all
   PASS). The challenge copies verbatim excerpts of FNE's and UPD's statement files plus the whole of
   ours, with four auxiliary commands: `setMainModule`; for the UPD excerpt,
   `respectTransparency=false` and `genMatcherCode=false`; and, new and for QB, emptying the
   auxiliary-proof cache before each copy.
4. Host memory: the guard never refused in sessions 8–10.
