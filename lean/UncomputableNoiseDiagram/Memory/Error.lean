/-
# Lemmas 7.1, 7.2 and 6.3 together: the data error bound (Mem3, Mem4 first step)

Node Mem3 (the union bound) of `BLUEPRINT.md` (Part A.7), NEW.

Paper (Theorem 7.3, proof): "Condition on the correct chart. Lemmas 6.3 and 7.2 bound every data
or second-coordinate error, uniformly in time, by `Σ_{g ≥ 1}(K_mem γ)^g < 1/4`, where the
inequality follows from the parameter choices in Section 9."

Formalization (at the selected parameters, for any chart data with `B = 4^k` lanes):
* `RM`, `SM`: the raw and statistical events of a projected label (empty off level `0`);
  **`joint_MP`** (Lemma 6.3 for projected labels: `≤ γ^{|G|}`);
* `sumOf_nonneg_lt`: the series `S = Σ_{g ≥ 0}(K_mem γ)^{g+1}` is summable, `0 ≤ S < 1/4`
  (`mem_series_lt`), and equals the `ℝ≥0∞` series;
* **`mem_bad_le`**: for any family of trajectories `Y ω` satisfying the hypotheses of Lemma 7.1
  for every noise `ω` (with the bin width `W = ⌊C/ε⌋` of (17)), the probability of a data error at
  `(w, t)` is at most `S < 1/4`, uniformly in `(w, t)`.
-/
import UncomputableNoiseDiagram.Memory.Derivation
import UncomputableNoiseDiagram.Sensors.Selected

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UND.Memory

open UND.Rule UND.Sensors UND.Raw UND.Param
open FNE (Plane)

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData B τ}

/-- The raw event of a projected label (empty off level `0`). -/
def RM (CD : ChartData B τ) (W : ℕ) (p : MP) : Set (PNoise CD) :=
  if p.2 = 0 then RawEv CD W p.1 else ∅

/-- The statistical event of a projected label (empty off level `0`). -/
def SM (CD : ChartData B τ) (tc tr : ℕ → Bool) (k s a W : ℕ) (p : MP) : Set (PNoise CD) :=
  if p.2 = 0 then StatEv CD tc tr k s a W p.1 else ∅

/-- `0 ≤ γ` and the memory series: `S = Σ_{g ≥ 0}(K_mem γ)^{g+1}` with `0 ≤ S < 1/4`. -/
theorem gamma_facts :
    0 ≤ gammaOf (4 ^ kParam) ∧ 0 ≤ (Kmem : ℝ) * gammaOf (4 ^ kParam) ∧
      (Kmem : ℝ) * gammaOf (4 ^ kParam) < 1 ∧
      ∑' g : ℕ, ((Kmem : ℝ) * gammaOf (4 ^ kParam)) ^ (g + 1) < 1 / 4 := by
  have hz : 4 * zB (4 ^ kParam) < 1 := bsearch_kParam.2.2.1
  have he : etaHat (4 ^ kParam) < ((((64 * Kmem : ℕ) : ℚ) ^ 6)⁻¹) :=
    lt_of_lt_of_le bsearch_kParam.2.2.2 (min_le_left _ _)
  obtain ⟨h0, h1⟩ := mem_gamma_lt hz he
  have hK : (0 : ℝ) < Kmem := by exact_mod_cast Kmem_pos
  refine ⟨?_, h0, by linarith, mem_series_lt hz he⟩
  by_contra hneg
  push Not at hneg
  have : (Kmem : ℝ) * gammaOf (4 ^ kParam) < 0 := mul_neg_of_pos_of_neg hK hneg
  linarith

/-- The `ℝ≥0∞` memory series is the real one. -/
theorem tsum_ofReal_mem :
    ∑' g : ℕ, ((Kmem : ℝ≥0∞) * ENNReal.ofReal (gammaOf (4 ^ kParam))) ^ (g + 1) =
      ENNReal.ofReal (∑' g : ℕ, ((Kmem : ℝ) * gammaOf (4 ^ kParam)) ^ (g + 1)) := by
  obtain ⟨hγ, hx0, hx1, -⟩ := gamma_facts
  set x := (Kmem : ℝ) * gammaOf (4 ^ kParam) with hx
  have e : (Kmem : ℝ≥0∞) * ENNReal.ofReal (gammaOf (4 ^ kParam)) = ENNReal.ofReal x := by
    rw [hx, ENNReal.ofReal_mul (Nat.cast_nonneg _), ENNReal.ofReal_natCast]
  have hs : Summable fun g : ℕ => x ^ (g + 1) := by
    have := (summable_geometric_of_lt_one hx0 hx1).mul_left x
    refine this.congr fun g => ?_
    ring
  rw [e, ENNReal.ofReal_tsum_of_nonneg (fun g => pow_nonneg hx0 _) hs]
  congr 1
  funext g
  rw [ENNReal.ofReal_pow hx0]

/-- **Lemma 6.3 for projected labels**: `P{R ∪ S at all labels of G} ≤ γ^{|G|}`. -/
theorem joint_MP {τ' : Type*} [Fintype τ'] [DecidableEq τ'] {CD : ChartData (4 ^ kParam) τ'}
    (G : (ISite → PhysSym CD) → (ISite → PhysSym CD)) (N : Finset ISite) {n : ℕ} (hn : 1 ≤ n)
    {ε : ℝ} (hε : ε ∈ UND.window loF hiF n) (tc tr : ℕ → Bool) (G' : Finset MP) :
    pLaw G N ε (⋂ p ∈ G', (RM CD ⌊(C : ℝ) / ε⌋₊ p ∪
      SM CD tc tr kParam sParam (n + n0Param) ⌊(C : ℝ) / ε⌋₊ p)) ≤
      ENNReal.ofReal (gammaOf (4 ^ kParam)) ^ G'.card := by
  classical
  set W := ⌊(C : ℝ) / ε⌋₊
  have hR := regime_final hn hε
  have hP := isProbabilityMeasure_pLaw G N hR.eps_nonneg hR.eps_le
  by_cases hall : ∀ p ∈ G', p.2 = 0
  · set L := G'.image Prod.fst with hL
    have hcard : L.card = G'.card := by
      refine Finset.card_image_of_injOn fun p hp p' hp' h => ?_
      exact Prod.ext h ((hall p hp).trans (hall p' hp').symm)
    have hset : (⋂ p ∈ G', (RM CD W p ∪ SM CD tc tr kParam sParam (n + n0Param) W p)) =
        ⋂ l ∈ L, (RawEv CD W l ∪ StatEv CD tc tr kParam sParam (n + n0Param) W l) := by
      ext ω
      simp only [Set.mem_iInter, hL, Finset.mem_image]
      constructor
      · rintro h l ⟨p, hp, rfl⟩
        have := h p hp
        simpa [RM, SM, hall p hp] using this
      · intro h p hp
        have := h p.1 ⟨p, hp, rfl⟩
        simpa [RM, SM, hall p hp] using this
    rw [hset, ← ofReal_measureReal (measure_ne_top _ _), ← hcard,
      ← ENNReal.ofReal_pow gamma_facts.1]
    exact ENNReal.ofReal_le_ofReal (joint_source_final G N hn hε tc tr L)
  · push Not at hall
    obtain ⟨p, hp, hp0⟩ := hall
    have hsub : (⋂ p ∈ G', (RM CD W p ∪ SM CD tc tr kParam sParam (n + n0Param) W p)) ⊆ ∅ := by
      intro ω hω
      have := Set.mem_iInter₂.1 hω p hp
      simp [RM, SM, hp0] at this
    rw [Set.subset_empty_iff.1 hsub, measure_empty]
    exact zero_le

/-- **The data error bound** (Lemmas 7.1, 7.2, 6.3; Theorem 7.3, first step): for trajectories
satisfying the hypotheses of Lemma 7.1 for every noise, with `W = ⌊C/ε⌋`, a data error at `(w, t)`
has probability at most `S = Σ_{g ≥ 1}(K_mem γ)^g < 1/4`. -/
theorem mem_bad_le {τ' : Type*} [Fintype τ'] [DecidableEq τ'] {CD : ChartData (4 ^ kParam) τ'}
    (G : (ISite → PhysSym CD) → (ISite → PhysSym CD)) (N : Finset ISite) {n : ℕ} (hn : 1 ≤ n)
    {ε : ℝ} (hε : ε ∈ UND.window loF hiF n) (tc tr : ℕ → Bool)
    (Y : PNoise CD → ℤ → PConfig CD) (ref : Plane → LiveLetter CD.toWangRel)
    (hY : ∀ ω, MCtx.Hyp ⟨Y ω, ω, ref, ⌊(C : ℝ) / ε⌋₊⟩ sParam tc tr kParam (n + n0Param))
    (w : ISite) (t : ℤ) :
    pLaw G N ε {ω | dataOf (Y ω t) w ≠ some (ref w.1)} ≤
      ENNReal.ofReal (∑' g : ℕ, ((Kmem : ℝ) * gammaOf (4 ^ kParam)) ^ (g + 1)) := by
  classical
  set W := ⌊(C : ℝ) / ε⌋₊ with hWdef
  have hR := regime_final hn hε
  have hW : 1 ≤ W := by
    have h1 := hR.epsW_ge
    have h2 := hR.C_pos
    rw [← hWdef] at h1
    by_contra h0
    have hW0 : W = 0 := by omega
    rw [hW0] at h1
    simp at h1
    linarith
  rw [← tsum_ofReal_mem]
  refine mem_union (pLaw G N ε) nbrM (108 * UND.Param.q + 6) card_nbrM_le (by omega)
    nbrM_le_Delta (fM W ((w, t), 0)) id (RM CD W) (SM CD tc tr kParam sParam (n + n0Param) W)
    _ (joint_MP G N hn hε tc tr) _ ?_
  intro ω hω
  obtain ⟨g, hg, K, A, hK, hA, hsrc⟩ :=
    MCtx.mem_cover (Γ := ⟨Y ω, ω, ref, W⟩) (hY ω) hW w t hω
  refine ⟨g, hg, K, A, hK, hA, fun v hv => ?_⟩
  obtain ⟨h0, hv'⟩ := hsrc v hv
  simpa [RM, SM, h0] using hv'

end UND.Memory
