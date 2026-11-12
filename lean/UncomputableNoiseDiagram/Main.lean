/-
# The final theorems

`UND.theorem_A : UND.TheoremA` (Theorem 9.3 / Theorem A): the memory branch (Theorem 7.3,
`Memory/Theorem.lean`) and the halting branch (Lemmas 8.1–8.4, `Forget/*.lean`, with Lemma 8.5,
`PCA/Pullback.lean`, `PCA/Attraction.lean`) assembled by `UND.Memory.theoremA_of_halting`.
Corollary 9.4 and the one-rule corollary are derived from it here with no further gap.
-/
import UncomputableNoiseDiagram.Corollary
import UncomputableNoiseDiagram.Memory.Theorem
import UncomputableNoiseDiagram.Forget.Halting

set_option autoImplicit false

namespace UND

/-- **Theorem 9.3 / Theorem A** (statement in `Statements.lean`): Theorem 7.3 when `U(n)` does
not halt; Lemma 8.4 (almost surely unique complete trajectories) and Lemma 8.5 when it halts. -/
theorem theorem_A : TheoremA := UND.Memory.theoremA_of_halting UND.Forget.halting_branch

/-- **Corollary 9.4** (statement in `Statements.lean`), from Theorem 9.3. -/
theorem corollary_9_4 : CorollaryNineFour := corollaryNineFour_of_theoremA theorem_A

/-- One fixed automaton on `ℤ⁶` with undecidable ergodicity at the rational rates of computable
disjoint windows. -/
theorem one_rule_undecidable : OneRuleUndecidable := oneRuleUndecidable_of_corollary corollary_9_4

end UND
