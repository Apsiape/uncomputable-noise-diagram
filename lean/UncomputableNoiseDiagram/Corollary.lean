/-
# Corollary 9.4 from Theorem 9.3, and one fixed undecidable rule

The proof of Corollary 9.4 as printed: "The midpoint `ε_n` is computable and rational. An
algorithm deciding the promised question at `ε_n` would decide whether `U(n)` halts by
Theorem 9.3."

* `midP`: the presentation `(a e + c b, 2 b e)` of the midpoint of `(a/b, c/e)`, computable from
  computable presentations of the endpoints;
* **`promiseUndecidable_of_noiseDiagram`**: for a universal `U`, the clauses of Theorem 9.3 give
  the promise undecidability of Corollary 9.4 for the same automaton and intervals;
* **`corollaryNineFour_of_theoremA`**: `TheoremA → CorollaryNineFour`;
* **`oneRuleUndecidable_of_corollary`**: with the hard-model core's universal machine
  (`UPD.Compiler.univMachine_universal`), `CorollaryNineFour → OneRuleUndecidable`.
-/
import UncomputableNoiseDiagram.Statements
import UndecidablePhaseDiagram.Compiler.Universal

set_option autoImplicit false

namespace UND

/-- The midpoint presentation: `(a/b + c/e)/2 = (a e + c b)/(2 b e)`. -/
def midP (p p' : ℕ × ℕ) : ℕ × ℕ := (p.1 * p'.2 + p'.1 * p.2, 2 * (p.2 * p'.2))

theorem midP_pos {p p' : ℕ × ℕ} (h : 0 < p.2) (h' : 0 < p'.2) : 0 < (midP p p').2 := by
  simp only [midP]; positivity

theorem midP_val {p p' : ℕ × ℕ} (h : 0 < p.2) (h' : 0 < p'.2) :
    ((midP p p').1 : ℝ) / (midP p p').2 = ((p.1 : ℝ) / p.2 + (p'.1 : ℝ) / p'.2) / 2 := by
  have hb : (p.2 : ℝ) ≠ 0 := by exact_mod_cast h.ne'
  have he : (p'.2 : ℝ) ≠ 0 := by exact_mod_cast h'.ne'
  simp only [midP]
  push_cast
  field_simp

theorem computable_midP {f f' : ℕ → ℕ × ℕ} (hf : Computable f) (hf' : Computable f') :
    Computable fun n => midP (f n) (f' n) := by
  have h1 : Computable fun n => (f n).1 := Computable.fst.comp hf
  have h2 : Computable fun n => (f n).2 := Computable.snd.comp hf
  have h3 : Computable fun n => (f' n).1 := Computable.fst.comp hf'
  have h4 : Computable fun n => (f' n).2 := Computable.snd.comp hf'
  have hmul := (Primrec.nat_mul).to_comp
  have hadd := (Primrec.nat_add).to_comp
  exact Computable.pair (hadd.comp (hmul.comp h1 h4) (hmul.comp h3 h2))
    (hmul.comp (Computable.const 2) (hmul.comp h2 h4))

/-- **Corollary 9.4 from the clauses of Theorem 9.3.** -/
theorem promiseUndecidable_of_noiseDiagram {U : UPD.Machine} (hU : UPD.Universal U) {A : CA 6}
    {lo hi : ℕ → ℚ} (h : NoiseDiagram U A lo hi) : PromiseUndecidable A lo hi := by
  rintro ⟨g, hg, hcorr⟩
  obtain ⟨⟨f, hf, hfp⟩, ⟨f', hf', hfp'⟩, hwin, -⟩ := h.1
  have key : ∀ n, 1 ≤ n → (g (midP (f n) (f' n)) = true ↔ U.HaltsOn n) := by
    intro n hn
    obtain ⟨hb, hlo⟩ := hfp n
    obtain ⟨he, hhi⟩ := hfp' n
    have hval := midP_val hb he
    have hlo' : ((f n).1 : ℝ) / (f n).2 = (lo n : ℝ) := by rw [← hlo]; push_cast; rfl
    have hhi' : ((f' n).1 : ℝ) / (f' n).2 = (hi n : ℝ) := by rw [← hhi]; push_cast; rfl
    rw [hlo', hhi'] at hval
    obtain ⟨_, hlh, _⟩ := hwin n hn
    have hlh' : (lo n : ℝ) < hi n := by exact_mod_cast hlh
    have hin : ((midP (f n) (f' n)).1 : ℝ) / (midP (f n) (f' n)).2 ∈ window lo hi n := by
      rw [hval]; constructor <;> linarith
    rw [hcorr n hn _ (midP_pos hb he) hin]
    exact (h.2 n hn _ hin).1
  apply hU
  refine ComputablePred.computable_iff.2
    ⟨fun n => decide (1 ≤ n) && g (midP (f n) (f' n)), ?_, ?_⟩
  · have hle : Computable fun n : ℕ => decide (1 ≤ n) :=
      (Primrec.nat_le.comp (Primrec.const 1) Primrec.id).decide.to_comp
    exact (Primrec.and.to_comp).comp hle (hg.comp (computable_midP hf hf'))
  · funext n
    simp only [Bool.and_eq_true, decide_eq_true_eq, eq_iff_iff]
    constructor
    · rintro ⟨hn, hh⟩; exact ⟨hn, (key n hn).2 hh⟩
    · rintro ⟨hn, hh⟩; exact ⟨hn, (key n hn).1 hh⟩

/-- **`TheoremA → CorollaryNineFour`.** -/
theorem corollaryNineFour_of_theoremA (h : TheoremA) : CorollaryNineFour := by
  intro U hU
  obtain ⟨A, lo, hi, hA⟩ := h U
  exact ⟨A, lo, hi, hA, promiseUndecidable_of_noiseDiagram hU hA⟩

/-- **`CorollaryNineFour → OneRuleUndecidable`**, with the universal machine of the hard-model
core. -/
theorem oneRuleUndecidable_of_corollary (h : CorollaryNineFour) : OneRuleUndecidable := by
  obtain ⟨A, lo, hi, hA, hP⟩ := h _ UPD.Compiler.univMachine_universal
  exact ⟨A, lo, hi, hA.1, hP⟩

end UND
