/-
# The noisy automaton (6) in the paper's coordinates (R6)

Node R6 of `BLUEPRINT.md` (Part A.2), NEW. The automaton `ruleCA` lives on `Fin |Σ|` and on
`Fin 6 → ℤ` (D5, D6). Sections 5–8 read its process in the paper's coordinates: sites
`(u, P) ∈ ℤ² × ℤ⁴` and symbols `Σ = 𝒜_R × 𝒜_R × ℋ^B`.

* `update_decode`: one noisy update of `caOf G N`, decoded, is "the replacement value where the
  flag is set, `G` elsewhere" (the paper's displayed update, for the proposal (6));
* `uniformLaw_decode`: the decoded replacement value is uniform on `Σ`
  (`P(Z ∈ E) = |E| / |Σ|`);
* `card_field_fiber`, **`uniformLaw_field`**: each helper field of the replacement mark is uniform
  on `ℋ` (`P = 1/100` for each letter), because (2) is a product (Section 6: "the replacement mark
  is uniform on `ℋ` because (2) is a product").
-/
import UncomputableNoiseDiagram.Rule.CA
import UncomputableNoiseDiagram.PCA.Process

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UND.Rule

variable {S : Type*} [Fintype S] [Nonempty S]

/-- Decoding a symbol of `Fin |Σ|`. -/
def decodeSym (a : Fin (Fintype.card S)) : S := (Fintype.equivFin S).symm a

/-- **One noisy update, decoded**: where the flag is set the decoded replacement value, elsewhere
`G` of the decoded configuration. -/
theorem update_decode (G : (ISite → S) → (ISite → S)) (N : Finset ISite)
    (htr : ∀ x a, G (fun w => x (w + a)) = fun w => G x (w + a))
    (hloc : ∀ x y w, (∀ z ∈ N, x (w + z) = y (w + z)) → G x w = G y w)
    (e : UND.Site 6 → Bool × Fin (Fintype.card S)) (x : UND.Site 6 → Fin (Fintype.card S)) :
    decodeConfig ((caOf G N).update e x) = fun w =>
      if (e (siteEquiv.symm w)).1 then decodeSym (e (siteEquiv.symm w)).2
      else G (decodeConfig x) w := by
  funext w
  unfold decodeConfig UND.CA.update
  split_ifs with h
  · rfl
  · rw [caOf_apply G N htr hloc, AddEquiv.apply_symm_apply, Equiv.symm_apply_apply]
    rfl

/-- The decoded replacement value is uniform on `Σ`: `P(Z ∈ E) = |E| / |Σ|`. -/
theorem uniformLaw_decode (G : (ISite → S) → (ISite → S)) (N : Finset ISite) (E : Finset S) :
    (caOf G N).uniformLaw (decodeSym ⁻¹' (E : Set S)) = (E.card : ℝ≥0∞) / Fintype.card S := by
  have hpre : (decodeSym ⁻¹' (E : Set S) : Set (Fin (Fintype.card S))) =
      ((E.map (Fintype.equivFin S).toEmbedding : Finset (Fin (Fintype.card S))) : Set _) := by
    ext a
    simp only [Set.mem_preimage, Finset.mem_coe, Finset.mem_map_equiv, decodeSym]
  change ((Fintype.card S : ℝ≥0∞)⁻¹ • (Measure.count : Measure (Fin (Fintype.card S))))
    (decodeSym ⁻¹' (E : Set S)) = _
  rw [hpre]
  simp only [Measure.smul_apply, Measure.count_apply_finset, Finset.card_map, smul_eq_mul]
  rw [ENNReal.div_eq_inv_mul]

/-! ## Helper fields of the replacement mark -/

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] (CD : ChartData B τ)

/-- Change helper field `j` by the transposition of `a` and `b`. -/
def swapField (j : Fin B) (a b : Helper) (σ : PhysSym CD) : PhysSym CD :=
  (σ.1, σ.2.1, fun i => if i = j then Equiv.swap a b (σ.2.2 i) else σ.2.2 i)

theorem swapField_swapField (j : Fin B) (a b : Helper) (σ : PhysSym CD) :
    swapField CD j a b (swapField CD j a b σ) = σ := by
  rcases σ with ⟨d, h, f⟩
  simp only [swapField, Prod.mk.injEq, true_and]
  funext i
  split_ifs <;> simp

/-- All letters occur equally often in field `j`. -/
theorem card_field_fiber_eq (j : Fin B) (a b : Helper) :
    (Finset.univ.filter (fun σ : PhysSym CD => σ.2.2 j = a)).card =
      (Finset.univ.filter (fun σ : PhysSym CD => σ.2.2 j = b)).card := by
  refine Finset.card_nbij' (swapField CD j a b) (swapField CD j a b) ?_ ?_ ?_ ?_
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    simp [swapField, hσ]
  · intro σ hσ
    simp only [Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_ofPred_eq] at hσ ⊢
    simp [swapField, hσ]
  · intro σ _
    exact swapField_swapField CD j a b σ
  · intro σ _
    exact swapField_swapField CD j a b σ

/-- Each helper letter occupies exactly a hundredth of `Σ` in field `j`. -/
theorem card_field_fiber (j : Fin B) (a : Helper) :
    (Finset.univ.filter (fun σ : PhysSym CD => σ.2.2 j = a)).card * 100 =
      Fintype.card (PhysSym CD) := by
  have h := Finset.card_eq_sum_card_fiberwise (s := (Finset.univ : Finset (PhysSym CD)))
    (t := (Finset.univ : Finset Helper)) (f := fun σ => σ.2.2 j) (fun _ _ => Finset.mem_univ _)
  rw [Finset.card_univ] at h
  rw [h, Finset.sum_congr rfl (fun b _ => card_field_fiber_eq CD j b a), Finset.sum_const,
    Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_comm]

/-- **Each helper field of the decoded replacement mark is uniform on `ℋ`** (Section 6: "the
replacement mark is uniform on `ℋ` because (2) is a product"). -/
theorem uniformLaw_field (G : (ISite → PhysSym CD) → (ISite → PhysSym CD)) (N : Finset ISite)
    (j : Fin B) (a : Helper) :
    (caOf G N).uniformLaw (decodeSym ⁻¹' {σ : PhysSym CD | σ.2.2 j = a}) = (100 : ℝ≥0∞)⁻¹ := by
  have hset : ({σ : PhysSym CD | σ.2.2 j = a} : Set (PhysSym CD)) =
      ((Finset.univ.filter (fun σ : PhysSym CD => σ.2.2 j = a) : Finset (PhysSym CD)) :
        Set (PhysSym CD)) := by
    ext σ
    simp
  rw [hset, uniformLaw_decode]
  set c := (Finset.univ.filter (fun σ : PhysSym CD => σ.2.2 j = a)).card with hc
  have hcard : Fintype.card (PhysSym CD) = c * 100 := (card_field_fiber CD j a).symm
  have hc0 : c ≠ 0 := by
    intro h0
    have := Fintype.card_pos (α := PhysSym CD)
    rw [hcard, h0] at this
    simp at this
  rw [hcard]
  push_cast
  rw [show (c : ℝ≥0∞) / (c * 100) = ((c : ℝ≥0∞) * 1) / (c * 100) by rw [mul_one],
    ENNReal.mul_div_mul_left _ _ (by exact_mod_cast hc0) (by simp), one_div]

end UND.Rule
