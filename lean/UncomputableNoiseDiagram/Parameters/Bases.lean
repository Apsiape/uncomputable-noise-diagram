/-
# Prop 9.2: the series bases

Part of node Q5 of `BLUEPRINT.md` (Part A.9). Prop 9.2: "The memory bound follows from
`K_mem √C = 1/128`, `K_mem η̂_B^{1/6} < 1/64`, so `K_mem γ < 1/32` and its geometric sum is below
`1/4`. The raw-path base `K_mem ε` is small under (27). … Finally, since `ε ≤ 1` and `M ≥ 1`,
`K_rare(N₀ε^M)^{1/16} ≤ N₀^{1/16}/(64(N₀+1)) < 1/64`."

* `Kmem_sqrt_C`: `K_mem √C = 1/128` (exact, from `C = (128K_mem)^{-2}`);
* `mem_eta_base` (for every `B` passing the conditions of (25)) and `mem_eta_base_kParam`:
  `K_mem η̂_B^{1/6} < 1/64`;
* `mem_gamma_lt`, `mem_series_lt`: `γ = √C + η̂_B^{1/6}`, `K_mem γ < 1/32` and
  `Σ_{g≥1} (K_mem γ)^g < 1/4`;
* `raw_base_lt`: `K_mem ε < 1/64` for `ε ≤ (64K_mem)^{-4}`;
* `rare_base_lt` (abstract in `K_rare`, `N₀`, `M`) and `rare_base_lt_epsStar`: the rare base is
  below `1/64` for `0 < ε ≤ ε_*`.
The history base waits for the compression (21) and bases (22) of Lemma 8.2. Kernel discipline
D13: every lemma is stated for abstract `B`, `K`, `N`; the selected constants enter by one-step
instantiation.
-/
import UncomputableNoiseDiagram.Parameters.Threshold
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

noncomputable section

namespace UND.Param

/-- Prop 9.2: `K_mem √C = 1/128`. -/
theorem Kmem_sqrt_C : (Kmem : ℝ) * Real.sqrt ((C : ℚ) : ℝ) = 1 / 128 := by
  have hK : (0 : ℝ) < Kmem := by exact_mod_cast Kmem_pos
  have hC : ((C : ℚ) : ℝ) = ((128 * (Kmem : ℝ))⁻¹) ^ 2 := by
    rw [C, cden]
    push_cast
    rw [inv_pow, one_div]
  rw [hC, Real.sqrt_sq (by positivity)]
  field_simp

/-- `η̂_B > 0` when `4 z_B < 1`. -/
theorem etaHat_pos {B : ℕ} (hz : 4 * zB B < 1) : 0 < etaHat B := by
  have hu : 0 < uB B := by unfold uB; positivity
  have hw : 0 < wB B := by unfold wB; positivity
  unfold etaHat
  have : 0 < 1 - 4 * zB B := by linarith
  positivity

/-- Prop 9.2: `K_mem η̂_B^{1/6} < 1/64` for every `B` with `4 z_B < 1` and
`η̂_B < (64K_mem)^{-6}`. -/
theorem mem_eta_base {B : ℕ} (hz : 4 * zB B < 1)
    (he : etaHat B < ((((64 * Kmem : ℕ) : ℚ) ^ 6)⁻¹)) :
    (Kmem : ℝ) * (((etaHat B : ℚ) : ℝ) ^ ((1 : ℝ) / 6)) < 1 / 64 := by
  have hK : (0 : ℝ) < Kmem := by exact_mod_cast Kmem_pos
  have h0 : (0 : ℝ) ≤ ((etaHat B : ℚ) : ℝ) := by exact_mod_cast (etaHat_pos hz).le
  have he' : ((etaHat B : ℚ) : ℝ) < ((64 * (Kmem : ℝ))⁻¹) ^ 6 := by
    have : ((etaHat B : ℚ) : ℝ) < (((((64 * Kmem : ℕ) : ℚ) ^ 6)⁻¹ : ℚ) : ℝ) := by
      exact_mod_cast he
    refine this.trans_eq ?_
    push_cast
    rw [inv_pow]
  have hr : ((etaHat B : ℚ) : ℝ) ^ ((1 : ℝ) / 6) < (64 * (Kmem : ℝ))⁻¹ := by
    have h1 := Real.rpow_lt_rpow h0 he' (by norm_num : (0 : ℝ) < 1 / 6)
    have h2 : (((64 * (Kmem : ℝ))⁻¹) ^ 6) ^ ((1 : ℝ) / 6) = (64 * (Kmem : ℝ))⁻¹ := by
      rw [show ((1 : ℝ) / 6) = ((6 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
    rwa [h2] at h1
  calc (Kmem : ℝ) * (((etaHat B : ℚ) : ℝ) ^ ((1 : ℝ) / 6))
      < (Kmem : ℝ) * (64 * (Kmem : ℝ))⁻¹ := mul_lt_mul_of_pos_left hr hK
    _ = 1 / 64 := by field_simp

/-- `K_mem η̂_B^{1/6} < 1/64` for the selected `B = 4^k` ((25)). -/
theorem mem_eta_base_kParam :
    (Kmem : ℝ) * (((etaHat (4 ^ kParam) : ℚ) : ℝ) ^ ((1 : ℝ) / 6)) < 1 / 64 :=
  mem_eta_base bsearch_kParam.2.2.1 (lt_of_lt_of_le bsearch_kParam.2.2.2 (min_le_left _ _))

/-- Lemma 6.3's base `γ = √C + η̂_B^{1/6}`. -/
def gammaOf (B : ℕ) : ℝ := Real.sqrt ((C : ℚ) : ℝ) + ((etaHat B : ℚ) : ℝ) ^ ((1 : ℝ) / 6)

/-- Prop 9.2: `K_mem γ < 1/32` (indeed `< 3/128`). -/
theorem mem_gamma_lt {B : ℕ} (hz : 4 * zB B < 1)
    (he : etaHat B < ((((64 * Kmem : ℕ) : ℚ) ^ 6)⁻¹)) :
    0 ≤ (Kmem : ℝ) * gammaOf B ∧ (Kmem : ℝ) * gammaOf B < 3 / 128 := by
  have hK : (0 : ℝ) ≤ Kmem := Nat.cast_nonneg _
  have h1 := Kmem_sqrt_C
  have h2 := mem_eta_base hz he
  have h3 : (0 : ℝ) ≤ ((etaHat B : ℚ) : ℝ) ^ ((1 : ℝ) / 6) :=
    Real.rpow_nonneg (by exact_mod_cast (etaHat_pos hz).le) _
  unfold gammaOf
  constructor
  · have : 0 ≤ Real.sqrt ((C : ℚ) : ℝ) := Real.sqrt_nonneg _
    positivity
  · rw [mul_add]
    linarith

/-- Prop 9.2, the memory bound: `Σ_{g≥1} (K_mem γ)^g < 1/4`. -/
theorem mem_series_lt {B : ℕ} (hz : 4 * zB B < 1)
    (he : etaHat B < ((((64 * Kmem : ℕ) : ℚ) ^ 6)⁻¹)) :
    ∑' g : ℕ, ((Kmem : ℝ) * gammaOf B) ^ (g + 1) < 1 / 4 := by
  obtain ⟨h0, h1⟩ := mem_gamma_lt hz he
  set x := (Kmem : ℝ) * gammaOf B
  have hx1 : x < 1 := by linarith
  have hsum : ∑' g : ℕ, x ^ (g + 1) = x * (1 - x)⁻¹ := by
    simp_rw [pow_succ', ← tsum_geometric_of_lt_one h0 hx1]
    exact tsum_mul_left
  rw [hsum]
  have : (1 - x)⁻¹ ≤ 128 / 125 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]
    linarith
  calc x * (1 - x)⁻¹ ≤ (3 / 128) * (128 / 125) := by
        apply mul_le_mul h1.le this (by positivity) (by norm_num)
    _ < 1 / 4 := by norm_num

/-- Prop 9.2, the raw-path base: `K_mem ε < 1/64` for `ε ≤ (64K_mem)^{-4}`. -/
theorem raw_base_lt {ε : ℝ} (hε : ε ≤ ((((64 * Kmem : ℕ) : ℚ) ^ 4)⁻¹ : ℚ)) :
    (Kmem : ℝ) * ε < 1 / 64 := by
  have hK : (1 : ℝ) ≤ Kmem := by exact_mod_cast Kmem_pos
  have hε' : ε ≤ ((64 * (Kmem : ℝ)) ^ 4)⁻¹ := by
    refine hε.trans (le_of_eq ?_)
    push_cast
    rfl
  have hpos : (0 : ℝ) < (64 * (Kmem : ℝ)) ^ 4 := by positivity
  calc (Kmem : ℝ) * ε ≤ (Kmem : ℝ) * ((64 * (Kmem : ℝ)) ^ 4)⁻¹ :=
        mul_le_mul_of_nonneg_left hε' (by positivity)
    _ < 1 / 64 := by
        rw [← div_eq_mul_inv, div_lt_iff₀ hpos]
        nlinarith [pow_le_pow_left₀ (by norm_num : (0 : ℝ) ≤ 1) hK 3]

/-- `N^{1/16} < N + 1` for every natural `N`. -/
theorem rpow_sixteenth_lt (N : ℕ) : (N : ℝ) ^ ((1 : ℝ) / 16) < N + 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp
  · have h1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
    have : (N : ℝ) ^ ((1 : ℝ) / 16) ≤ (N : ℝ) ^ (1 : ℝ) :=
      Real.rpow_le_rpow_of_exponent_le h1 (by norm_num)
    rw [Real.rpow_one] at this
    linarith

/-- Prop 9.2, the rare base, abstract in `K_rare = K ≥ 1`, `N₀ = N` and `M ≥ 1`: for
`0 < ε ≤ 1` with `ε ≤ [64K(N+1)]^{-16}`, `K(Nε^M)^{1/16} < 1/64`. -/
theorem rare_base_lt (K N M : ℕ) (hK : 1 ≤ K) (hM : 1 ≤ M) {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1)
    (hε : ε ≤ ((64 * (K : ℝ) * (N + 1)) ^ 16)⁻¹) :
    (K : ℝ) * ((N : ℝ) * ε ^ M) ^ ((1 : ℝ) / 16) < 1 / 64 := by
  have hKr : (1 : ℝ) ≤ K := by exact_mod_cast hK
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg _
  have hD : (0 : ℝ) < 64 * (K : ℝ) * (N + 1) := by positivity
  -- `ε^M ≤ ε`
  have hpow : ε ^ M ≤ ε := by
    calc ε ^ M ≤ ε ^ 1 := pow_le_pow_of_le_one h0.le h1 hM
      _ = ε := pow_one ε
  -- `ε^{1/16} ≤ [64K(N+1)]^{-1}`
  have hroot : ε ^ ((1 : ℝ) / 16) ≤ (64 * (K : ℝ) * (N + 1))⁻¹ := by
    have h := Real.rpow_le_rpow h0.le hε (by norm_num : (0 : ℝ) ≤ 1 / 16)
    have h2 : (((64 * (K : ℝ) * (N + 1)) ^ 16)⁻¹) ^ ((1 : ℝ) / 16) =
        (64 * (K : ℝ) * (N + 1))⁻¹ := by
      rw [← inv_pow, show ((1 : ℝ) / 16) = ((16 : ℕ) : ℝ)⁻¹ by norm_num]
      exact Real.pow_rpow_inv_natCast (by positivity) (by norm_num)
    rwa [h2] at h
  have hmono : ((N : ℝ) * ε ^ M) ^ ((1 : ℝ) / 16) ≤ ((N : ℝ) * ε) ^ ((1 : ℝ) / 16) :=
    Real.rpow_le_rpow (by positivity) (mul_le_mul_of_nonneg_left hpow hN0) (by norm_num)
  have hsplit : ((N : ℝ) * ε) ^ ((1 : ℝ) / 16) =
      (N : ℝ) ^ ((1 : ℝ) / 16) * ε ^ ((1 : ℝ) / 16) := Real.mul_rpow hN0 h0.le
  have hNr := rpow_sixteenth_lt N
  have hNr0 : (0 : ℝ) ≤ (N : ℝ) ^ ((1 : ℝ) / 16) := Real.rpow_nonneg hN0 _
  have key : (N : ℝ) ^ ((1 : ℝ) / 16) * ε ^ ((1 : ℝ) / 16) <
      (N + 1) * (64 * (K : ℝ) * (N + 1))⁻¹ := by
    calc (N : ℝ) ^ ((1 : ℝ) / 16) * ε ^ ((1 : ℝ) / 16)
        ≤ (N : ℝ) ^ ((1 : ℝ) / 16) * (64 * (K : ℝ) * (N + 1))⁻¹ :=
          mul_le_mul_of_nonneg_left hroot hNr0
      _ < (N + 1) * (64 * (K : ℝ) * (N + 1))⁻¹ :=
          mul_lt_mul_of_pos_right hNr (inv_pos.2 hD)
  have hfin : (K : ℝ) * ((N + 1) * (64 * (K : ℝ) * (N + 1))⁻¹) = 1 / 64 := by
    field_simp
  calc (K : ℝ) * ((N : ℝ) * ε ^ M) ^ ((1 : ℝ) / 16)
      ≤ (K : ℝ) * ((N : ℝ) * ε) ^ ((1 : ℝ) / 16) :=
        mul_le_mul_of_nonneg_left hmono (by positivity)
    _ = (K : ℝ) * ((N : ℝ) ^ ((1 : ℝ) / 16) * ε ^ ((1 : ℝ) / 16)) := by rw [hsplit]
    _ < (K : ℝ) * ((N + 1) * (64 * (K : ℝ) * (N + 1))⁻¹) :=
        mul_lt_mul_of_pos_left key (by positivity)
    _ = 1 / 64 := hfin

/-- Prop 9.2, the rare base at the selected constants, abstractly: for every `B` and `N`, every
`0 < ε ≤ 1` below `ε_*(B, N)` satisfies `K_rare(B)(Nε^M)^{1/16} < 1/64` (`M = 196608`). -/
theorem rare_base_lt_epsStarOf (B N : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1)
    (hε : ε ≤ ((epsStarOf B N : ℚ) : ℝ)) :
    (KrareOf B : ℝ) * ((N : ℝ) * ε ^ M) ^ ((1 : ℝ) / 16) < 1 / 64 := by
  refine rare_base_lt (KrareOf B) N M (KrareOf_pos B) (by unfold M h K; norm_num) h0 h1
    (hε.trans ?_)
  have := epsStarOf_le_rare B N
  have h' : ((epsStarOf B N : ℚ) : ℝ) ≤
      (((((64 * KrareOf B * (N + 1) : ℕ) : ℚ) ^ 16)⁻¹ : ℚ) : ℝ) := by exact_mod_cast this
  refine h'.trans (le_of_eq ?_)
  push_cast
  rfl

end UND.Param

end
