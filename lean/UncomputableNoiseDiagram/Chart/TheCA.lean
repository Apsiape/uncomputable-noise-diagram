/-
# The automaton of Theorem 9.3 (`theCA U`)

Nodes R5 (instance) and Q7 (hook) of `BLUEPRINT.md`, NEW. The machine `P` of Section 4.1
(`Machine/P.lean`) supplies the content data of the routing alphabet `R` (`Chart/Routing.lean`);
the rule (6) on `R` with `B = 4^k` lanes and threshold `s` is the automaton of Prop 2.1
(`Rule/CA.lean`). Kernel discipline (D13): the automaton is a function `theCAOf U n₀ k s` of its
parameters; the selected parameters `n₀`, `k`, `s` of Section 9 enter in one step (`theCA U`).

Paper (Section 9, proof of Theorem 9.3): "The rule is fixed and computably specified by
Propositions 2.1 and 9.2." (F9: "computably specified" is not rendered.)

* `contentP U n0`: the content data of `P` (`init`, `f_P`, HALT, the read-only tracks `h_in`, `π`);
* `theCAOf U n0 k s`, **`theCA U`**;
* **`prop_2_1_theCAOf`**: Prop 2.1 for it (global map (6), at most `κ = 2B(n_A + n_Q + 2)` parents
  with `B = 4^k`);
* **`theoremA_of_theCA`**: Theorem 9.3 follows from its two branches for `theCA U`.
-/
import UncomputableNoiseDiagram.Chart.Routing
import UncomputableNoiseDiagram.Machine.P
import UncomputableNoiseDiagram.Rule.CA
import UncomputableNoiseDiagram.Assembly

set_option autoImplicit false

noncomputable section

namespace UND

open UPD

/-- The content data of the machine `P` (Section 4.1) for the routing alphabet. -/
def Chart.contentP (U : Machine) (n0 : ℕ) : Chart.ContentOps (MachineP.Cell U n0) where
  init := MachineP.initP U n0
  fP := MachineP.fP U n0
  halts := MachineP.CarriesHalt U n0
  hin s := s.1.hin
  piBit s := s.1.pi

/-- The automaton (6) for `U`, with the parameters `n₀`, `k` (`B = 4^k`) and `s` as variables. -/
def theCAOf (U : Machine) (n0 k s : ℕ) : CA 6 :=
  Rule.ruleCA (Chart.chartData (Chart.contentP U n0) k) s

/-- **The automaton of Theorem 9.3**, with the parameters selected in Section 9. -/
def theCA (U : Machine) : CA 6 := theCAOf U Param.n0Param Param.kParam Param.sParam

/-- **Prop 2.1 for the automaton**: its global map is the proposal (6), and it has at most
`κ = 2B(n_A + n_Q + 2)` parents in both dependency directions together, `B = 4^k`. -/
theorem prop_2_1_theCAOf (U : Machine) (n0 k s : ℕ) :
    (∀ x w6, (theCAOf U n0 k s).apply x w6 =
      Fintype.equivFin (Rule.PhysSym (Chart.chartData (Chart.contentP U n0) k))
        (Rule.proposal s (Rule.decodeConfig x) (Rule.siteEquiv w6))) ∧
    2 * (theCAOf U n0 k s).nbhd.card ≤ Param.kappa (4 ^ k) :=
  Rule.prop_2_1 _ s (Nat.one_le_pow _ _ (by norm_num))

/-- **Theorem 9.3 from its two branches for `theCA U`** (memory when `U(n)` does not halt, almost
surely unique complete trajectories when it halts, on the final windows). -/
theorem theoremA_of_theCA (h : ∀ U : Machine, Branches U (theCA U)) : TheoremA :=
  theoremA_of_branches fun U => ⟨theCA U, h U⟩

end UND
