/-
# The assembly hook of Theorem 9.3 (Q7, reduction form)

Node Q7 of `BLUEPRINT.md` (Part A.9). The proof of Theorem 9.3 (Section 9): "Prop 2.1 and Prop 9.2
fix the rule. If `U(n)` does not halt, Theorem 7.3 gives two translation-invariant stationary laws.
If it halts, Lemma 8.4 gives uniqueness of complete trajectories and Lemma 8.5 gives the pullback
clause and attraction. The window arithmetic is (17)."

Here the final step is proved as a reduction, with the two branch statements as the premises of a
theorem (not as named hypotheses; they are the conclusions of Theorem 7.3 and Lemma 8.4 to be
proved):

* `Branches U A`: for every `n ≥ 1` and `ε ∈ I_n` (the final windows `loF`, `hiF` of (17), (28)):
  if `U(n)` does not halt, two translation-invariant initial laws with memory between them (the
  bit-0 and bit-1 initializations of Section 7; `HasMemoryFrom`, D12); if `U(n)` halts, almost
  surely any two complete common-noise trajectories agree at time `0` (Lemma 8.4, D15);
* **`noiseDiagram_of_branches`**: `Branches U A → NoiseDiagram U A loF hiF` (through
  `hasTwoTIStationaryLaws_of_memory`, `forgets_of_unique`, `pullbackEventuallySingleton_of_unique`,
  `noiseDiagram_clauses`, `isWindowFamily_final`, `0 < ε < 1` on the windows);
* **`theoremA_of_branches`**: `(∀ U, ∃ A, Branches U A) → TheoremA`.
The final proof will be `theoremA_of_branches (fun U => ⟨ruleCA (chartData U) sParam, …⟩)`.
-/
import UncomputableNoiseDiagram.PCA.Attraction
import UncomputableNoiseDiagram.PCA.ForgetErgodic
import UncomputableNoiseDiagram.Parameters.Threshold

set_option autoImplicit false

noncomputable section

open MeasureTheory

namespace UND

/-- The two branches of Theorem 9.3 for a machine `U` and an automaton `A` on the final windows:
memory between two translation-invariant initial laws when `U(n)` does not halt (Theorem 7.3),
almost sure uniqueness of complete trajectories at time `0` when it halts (Lemma 8.4). -/
def Branches (U : UPD.Machine) (A : CA 6) : Prop :=
  ∀ n : ℕ, 1 ≤ n → ∀ ε ∈ window Param.loF Param.hiF n,
    (¬ U.HaltsOn n → ∃ μ μ' : Measure A.Config, IsProbabilityMeasure μ ∧ IsProbabilityMeasure μ' ∧
      A.IsTranslationInvariant μ ∧ A.IsTranslationInvariant μ' ∧ A.HasMemoryFrom ε μ μ') ∧
    (U.HaltsOn n → ∀ᵐ ω ∂(A.noiseLaw₂ ε), ∀ X Y : ℤ → A.Config,
      A.IsComplete ω X → A.IsComplete ω Y → X 0 = Y 0)

/-- Rates in the final windows lie in `(0, 1)`. -/
theorem window_rate {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : ε ∈ window Param.loF Param.hiF n) :
    0 ≤ ε ∧ ε ≤ 1 := by
  have hfam := Param.isWindowFamily_final.2.2.1 n hn
  have h1 : (0 : ℝ) < (Param.loF n : ℝ) := by exact_mod_cast hfam.1
  have h2 : ((Param.hiF n : ℚ) : ℝ) < 1 := by exact_mod_cast hfam.2.2
  exact ⟨(h1.trans hε.1).le, (hε.2.trans h2).le⟩

/-- **Theorem 9.3 from its two branches**: the noise diagram holds on the final windows. -/
theorem noiseDiagram_of_branches (U : UPD.Machine) (A : CA 6) (h : Branches U A) :
    NoiseDiagram U A Param.loF Param.hiF := by
  refine ⟨Param.isWindowFamily_final, fun n hn ε hε => ?_⟩
  obtain ⟨h0, h1⟩ := window_rate hn hε
  obtain ⟨hnon, hhalt⟩ := h n hn ε hε
  refine A.noiseDiagram_clauses h0 h1 (P := U.HaltsOn n) (fun hU => ?_) (fun hU => ?_)
  · obtain ⟨μ, μ', hμ, hμ', hti, hti', hmem⟩ := hnon hU
    exact A.hasTwoTIStationaryLaws_of_memory h0 h1 hti hti' hmem
  · exact ⟨A.forgets_of_unique h0 h1 (hhalt hU), A.pullbackEventuallySingleton_of_unique (hhalt hU)⟩

/-- **Theorem A from the branches**: if every machine has an automaton satisfying both branches on
the final windows, Theorem 9.3 holds. -/
theorem theoremA_of_branches (h : ∀ U : UPD.Machine, ∃ A : CA 6, Branches U A) : TheoremA := by
  intro U
  obtain ⟨A, hA⟩ := h U
  exact ⟨A, Param.loF, Param.hiF, noiseDiagram_of_branches U A hA⟩

end UND
