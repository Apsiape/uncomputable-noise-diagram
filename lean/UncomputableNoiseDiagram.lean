/-
# Root module

Lean formalization of the core of S. Douglas and N. Mghirbi, "One noisy cellular automaton with
an uncomputable noise diagram", v1.1.0 (Zenodo DOI 10.5281/zenodo.24152233; Theorem A, Theorem 9.3
and Corollary 9.4 are printed identically in v1.0.0, DOI 10.5281/zenodo.24147269): Theorem 9.3
(Theorem A) and Corollary 9.4, end to end, with no `sorry` and no named hypotheses.

* `Statements.lean`: the statement of record (`UND.TheoremA`, `UND.CorollaryNineFour`,
  `UND.OneRuleUndecidable`) and every definition it uses;
* `Main.lean`: `UND.theorem_A` (closed in session 10: the memory branch, Theorem 7.3, and the
  halting branch, Section 8, assembled by `UND.Memory.theoremA_of_halting`), `UND.corollary_9_4`,
  `UND.one_rule_undecidable` (derived from it, `Corollary.lean`); all three depend only on
  `propext`, `Classical.choice`, `Quot.sound`;
* `Windows.lean`: the intervals (17) are a computable disjoint window family;
* `Parameters/Geometry.lean`: the fixed geometry and exact integer constants;
* `Parameters/Search.lean`: the search (25) for `B = 4^k` (`kParam`, and `kParam = 52386`);
* `Contour/Grouped.lean`: Lemma 5.1 (grouped terminal estimate), abstract form: the copied-arm
  witness, the edge bound (12), connectivity, singleton groups, the span;
* `Chart/BlackType.lean`: the black-type rank comparison and the abstract cutoff lemma;
* `Parameters/Threshold.lean`: `ε_*` (27), the search (28) for `n₀`, the final intervals, and
  the interval clauses of Prop 9.2 (placement below `ε_*`, `a ≥ k + 3`, ruler margins (18));
* `Parameters/Bases.lean`: the series bases of Prop 9.2 (memory, raw-path and rare bases);
* `Contour/Counting.lean`: Lemma 9.1 (literal encoding bounds: connected edge sets with a marked
  source subset, `≤ 4(2Δ²)^N`, `≤ K_mem^g`, `≤ K_rare^g`), the union bound over encodings, and the
  hook from the copied-arm witness of Lemma 5.1;
* `Rule/Checker.lean`, `Rule/Proposal.lean`, `Rule/CA.lean`: the rule of Section 2 generic in the
  chart tile set (D4): chart letters, the checker `F_R` with the provider threshold, the helper
  alphabet, drivers (3), fields (4), `Pin` (5), the proposal (6), and Prop 2.1 (one finite-range
  automaton on `ℤ⁶`, at most `κ` parents);
* `Rule/Noise.lean`: the noisy automaton (6) read in the paper's coordinates (decoded update,
  uniform replacement mark, uniform helper fields);
* `Chart/LanePhase.lean`: the lane phase (9) on finite bottom rows, and the phase-zero gate
  classification in its restricted form (fidelity deviation FD2);
* `Chart/Walls.lean`: the light-wall classification at a finite-rank coordinate in every phase,
  and `R_d - L_d = ℓ_d`;
* `Chart/Origins.lean`: finite parent ranks `≤ 2d` in a closed frame (Lemma 3.3, first step);
  `Orig`, `End` and the gates on finite bottom rows;
* `Chart/Decorated.lean`: the decorated scaffold (rank flags `V`, `H_row`, filter (8)) and
  Lemma 3.2 (one common nonincreasing cutoff; every finite cutoff occurs);
* `Chart/PhaseTable.lean`: the lane-phase lookup table on central words of radius `ρ_{2k}` (D7);
  it reads the lane phase (9) on every tiling, in every phase;
* `Machine/P.lean`: the direct finite machine `P` of Section 4.1 (program, `δ_P`, the content
  alphabet `S_P`, the ordered local rule `f_P`, `init`);
* `Chart/Routing.lean`: the routing alphabet `R` of Section 3.3 ((O1)–(E3), (K1)–(K3), (C0), the
  tableau (10), the phase extension) and its chart data for the controller;
* `Chart/TheCA.lean`: the automaton `theCA U` of Theorem 9.3 (Prop 2.1 for it), and Theorem 9.3
  from its two branches for `theCA U`;
* `Chart/RChart.lean`: legal charts of `R` (projections to decorated and quarter tilings, the
  central words are the true words, the decoded phase is the lane phase, the gate on finite bottom
  rows);
* `Chart/Board.lean`, `Chart/BoardGaps.lean`, `Chart/BoardFlags.lean`, `Chart/BoardTableau.lean`:
  Lemma 3.3 (finite-board forcing in every phase): walls and orientation on free lines, free ×
  free sites active, non-free lines carry one direction (the laminar argument), the exact boundary
  flags, channels, records and the recursion `s_{i+1}(j) = f_P(s_i(j-1), s_i(j), s_i(j+1))`;
* `Chart/Input.lean`: Lemma 4.2 (ranks of free coordinates; the initial zero of a large board is at
  index `2^{a+1} - 2` with odd rank, every zero of a small board has even rank; every phase);
* `Machine/Run.lean`: Lemma 4.1(a) (the board recursion with `f_P` is the sequential machine `P`);
* `Machine/Scan.lean`, `Machine/Passes.lean`, `Machine/Decode.lean`: Lemma 4.1(b) (SCAN and the parity
  guard, the halving passes, SKIP, FINDN/APPENDU, RUN simulating `U`; the run halts iff `U` halts on
  the decoded input);
* `Chart/BoardRun.lean`: Lemma 3.3 indexed (a board carries the run of `P`);
* `Chart/Halting.lean`: Prop 4.3, halting branch (a wrong critical flag in every legal chart, every
  phase);
* `Chart/NonHalting.lean`: Prop 4.3, nonhalting branch, first part (under the correct cutoff no
  board of any depth halts);
* `Assembly.lean`: Theorem 9.3 from its two branches (memory when `U(n)` does not halt, unique
  complete trajectories when it halts) on the final windows;
* `PCA/Process.lean`, `PCA/Markov.lean`, `PCA/Cylinder.lean`, `PCA/Feller.lean`,
  `PCA/Translation.lean`, `PCA/ForgetErgodic.lean`, …: the generic PCA layer (noise laws, locality,
  measurability, `law`, the one-step product form, the Markov property, cylinders and window
  total variation, coupling, the Feller property and Cesàro limits, translation invariance,
  forgetting implies ergodicity, memory gives two translation-invariant stationary laws), ported
  from the forgetting core; `PCA/Pullback.lean`, `PCA/Attraction.lean`: Lemma 8.5 (complete
  trajectories, nested pullback images, time homogeneity of the two-sided noise; almost surely
  unique complete trajectories give the pullback clause and ergodicity);
* `Chart/Construct.lean`, `Chart/ChartLaw.lean`: Prop 4.3, nonhalting branch (the chart of a
  typical phase and its translation-invariant law);
* `Contour/Coherence.lean`, `Contour/RawPaths.lean`, `Contour/Deep.lean`: Lemmas 5.3, 5.2, 5.4;
* `Sensors/*.lean`: Section 6 (Lemmas 6.1–6.3, the laws (14), (15), the selected parameters);
* `Memory/*.lean`: Section 7 (Lemmas 7.1–7.2, the stationary helper initialization, Theorem 7.3);
* `Forget/*.lean`: Section 8 (Lemmas 8.1, 8.2, 8.4 and the halting branch; Lemma 8.3 is not
  needed, see `STATUS.md`, F21–F22).

Reused libraries: the forgetting core (`FixedNoiseErgodicity`) and the hard-model core
(`UndecidablePhaseDiagram`), both on the release pin Lean v4.35.0 / Mathlib `56a0058`. The
development imports them as prebuilt .olean trees (`scripts/env.sh`); the release package vendors
their sources under `vendor/` and compiles them (`README-ARXIV.md`).
-/
import UncomputableNoiseDiagram.Main
import UncomputableNoiseDiagram.Windows
import UncomputableNoiseDiagram.Parameters.Geometry
import UncomputableNoiseDiagram.Parameters.Search
import UncomputableNoiseDiagram.Chart.BlackType
import UncomputableNoiseDiagram.Contour.Grouped
import UncomputableNoiseDiagram.Parameters.Threshold
import UncomputableNoiseDiagram.Parameters.Bases
import UncomputableNoiseDiagram.PCA.Attraction
import UncomputableNoiseDiagram.Contour.Counting
import UncomputableNoiseDiagram.Rule.CA
import UncomputableNoiseDiagram.Assembly
import UncomputableNoiseDiagram.Rule.Noise
import UncomputableNoiseDiagram.Chart.LanePhase
import UncomputableNoiseDiagram.Chart.Walls
import UncomputableNoiseDiagram.Chart.Origins
import UncomputableNoiseDiagram.Chart.Decorated
import UncomputableNoiseDiagram.Chart.PhaseTable
import UncomputableNoiseDiagram.Machine.P
import UncomputableNoiseDiagram.Chart.Routing
import UncomputableNoiseDiagram.Chart.TheCA
import UncomputableNoiseDiagram.Chart.RChart
import UncomputableNoiseDiagram.Chart.Board
import UncomputableNoiseDiagram.Chart.BoardGaps
import UncomputableNoiseDiagram.Chart.BoardFlags
import UncomputableNoiseDiagram.Chart.BoardTableau
import UncomputableNoiseDiagram.Chart.Input
import UncomputableNoiseDiagram.Machine.Run
import UncomputableNoiseDiagram.Machine.Scan
import UncomputableNoiseDiagram.Machine.Passes
import UncomputableNoiseDiagram.Machine.Decode
import UncomputableNoiseDiagram.Chart.BoardRun
import UncomputableNoiseDiagram.Chart.Halting
import UncomputableNoiseDiagram.Chart.NonHalting
import UncomputableNoiseDiagram.Chart.Construct
import UncomputableNoiseDiagram.Chart.ChartLaw
import UncomputableNoiseDiagram.Contour.Coherence
import UncomputableNoiseDiagram.Contour.RawPaths
import UncomputableNoiseDiagram.Contour.Deep
import UncomputableNoiseDiagram.Sensors.Tails
import UncomputableNoiseDiagram.Sensors.Ideal
import UncomputableNoiseDiagram.Sensors.Ownership
import UncomputableNoiseDiagram.Sensors.Gate
import UncomputableNoiseDiagram.Sensors.Joint
import UncomputableNoiseDiagram.Sensors.Selected
import UncomputableNoiseDiagram.Memory.Count
import UncomputableNoiseDiagram.Memory.Ride
import UncomputableNoiseDiagram.Memory.Derivation
import UncomputableNoiseDiagram.Memory.Error
import UncomputableNoiseDiagram.Memory.RefChart
import UncomputableNoiseDiagram.Memory.Init
import UncomputableNoiseDiagram.Memory.InitLaw
import UncomputableNoiseDiagram.Memory.Theorem
import UncomputableNoiseDiagram.Forget.Miss
import UncomputableNoiseDiagram.Forget.Gate
import UncomputableNoiseDiagram.Forget.History
import UncomputableNoiseDiagram.Forget.HistBase
import UncomputableNoiseDiagram.Forget.Eliminate
import UncomputableNoiseDiagram.Forget.Coupling
import UncomputableNoiseDiagram.Forget.Halting

set_option autoImplicit false
