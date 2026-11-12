/-
# The search (25) for `B = 4^k` (Section 9)

"Choose the least `k ≥ 1` with `B = 4^k ≥ 20/C`, `4z_B < 1`, and
`η̂_B < min{(64K_mem)^{-6}, (64K_hist)^{-4}}`" (25), with `C = (128 K_mem)^{-2}` (24) and the
rationals of Lemma 6.2: `u_B = 2^{-⌊3BC/100⌋}`, `z_B = 2^{-⌊BC/3⌋}`, `w_B = 2^{-⌊BC²/50⌋}`,
`η̂_B = 3u_B/(1 - 4z_B) + 2w_B`.

* `BSearch k`: the printed predicate, over `ℚ`;
* the floors are natural-number quotients (`floor_zB`, `floor_uB`, `floor_wB`), so every
  comparison reduces to natural-number arithmetic on numbers of at most about `3·10⁵` bits, which
  the kernel evaluates (GMP); no power `2^{⌊3BC/100⌋}` (about `10^{15771}` bits) is ever built;
* **`bsearch_52386`**: `k = 52386` satisfies (25) (`w = ⌊BC²/50⌋ = 322199`, and
  `3(64K_mem)^6, 3(64K_hist)^4 < 2^w`);
* **`not_bsearch_of_lt`**: no `k < 52386` does (`η̂_B > 2w_B ≥ 2^{-80548} ≥ (64K_mem)^{-6}`, by
  monotonicity of `⌊BC²/50⌋` and `⌊4^{52385}C²/50⌋ = 80549`);
* **`kParam`** `:= Nat.find` (the least `k`, as printed) and **`kParam_eq : kParam = 52386`**, the
  value in the Scale paragraph (`verification/scale_check.py`).
-/
import UncomputableNoiseDiagram.Parameters.Geometry
import Mathlib.Data.Rat.Floor
import Mathlib.Algebra.Order.Field.Power

set_option autoImplicit false

namespace UND.Param

/-- (24): the denominator of `C = (128 K_mem)^{-2}`. -/
def cden : ℕ := (128 * Kmem) ^ 2

/-- (24): `C = (128 K_mem)^{-2}`. -/
noncomputable def C : ℚ := 1 / (cden : ℚ)

/-- Lemma 6.2: `u_B = 2^{-⌊3BC/100⌋}`. -/
noncomputable def uB (B : ℕ) : ℚ := (2 : ℚ) ^ (-⌊3 * (B : ℚ) * C / 100⌋)

/-- Lemma 6.2: `z_B = 2^{-⌊BC/3⌋}`. -/
noncomputable def zB (B : ℕ) : ℚ := (2 : ℚ) ^ (-⌊(B : ℚ) * C / 3⌋)

/-- Lemma 6.2: `w_B = 2^{-⌊BC²/50⌋}`. -/
noncomputable def wB (B : ℕ) : ℚ := (2 : ℚ) ^ (-⌊(B : ℚ) * C ^ 2 / 50⌋)

/-- Lemma 6.2: `η̂_B = 3u_B/(1 - 4z_B) + 2w_B`. -/
noncomputable def etaHat (B : ℕ) : ℚ := 3 * uB B / (1 - 4 * zB B) + 2 * wB B

/-- (25): the conditions on `k`. -/
def BSearch (k : ℕ) : Prop :=
  1 ≤ k ∧ 20 / C ≤ ((4 ^ k : ℕ) : ℚ) ∧ 4 * zB (4 ^ k) < 1 ∧
    etaHat (4 ^ k) < min ((((64 * Kmem : ℕ) : ℚ) ^ 6)⁻¹) ((((64 * Khist : ℕ) : ℚ) ^ 4)⁻¹)

theorem Delta_pos : 0 < Delta := by unfold Delta; positivity

theorem Kmem_pos : 0 < Kmem :=
  Nat.mul_pos (by norm_num) (pow_pos (Nat.mul_pos (by norm_num) (pow_pos Delta_pos 2)) _)

theorem Khist_pos : 0 < Khist :=
  Nat.mul_pos (Nat.mul_pos (by norm_num) (pow_pos (by unfold V L m; norm_num) _))
    (pow_pos (Nat.mul_pos (by norm_num) (pow_pos Delta_pos 2)) _)

theorem cden_pos : 0 < cden := pow_pos (Nat.mul_pos (by norm_num) Kmem_pos) 2

/-! ## The floors as natural-number quotients -/

theorem floor_zB (B : ℕ) : ⌊(B : ℚ) * C / 3⌋ = ((B / (3 * cden) : ℕ) : ℤ) := by
  have h : (B : ℚ) * C / 3 = ((B : ℕ) : ℚ) / ((3 * cden : ℕ) : ℚ) := by
    have : (cden : ℚ) ≠ 0 := by exact_mod_cast cden_pos.ne'
    simp only [C]; push_cast; field_simp
  rw [h, Rat.floor_natCast_div_natCast]; norm_cast

theorem floor_uB (B : ℕ) : ⌊3 * (B : ℚ) * C / 100⌋ = ((3 * B / (100 * cden) : ℕ) : ℤ) := by
  have h : 3 * (B : ℚ) * C / 100 = ((3 * B : ℕ) : ℚ) / ((100 * cden : ℕ) : ℚ) := by
    have : (cden : ℚ) ≠ 0 := by exact_mod_cast cden_pos.ne'
    simp only [C]; push_cast; field_simp
  rw [h, Rat.floor_natCast_div_natCast]; norm_cast

theorem floor_wB (B : ℕ) : ⌊(B : ℚ) * C ^ 2 / 50⌋ = ((B / (50 * cden ^ 2) : ℕ) : ℤ) := by
  have h : (B : ℚ) * C ^ 2 / 50 = ((B : ℕ) : ℚ) / ((50 * cden ^ 2 : ℕ) : ℚ) := by
    have : (cden : ℚ) ≠ 0 := by exact_mod_cast cden_pos.ne'
    simp only [C]; push_cast; field_simp
  rw [h, Rat.floor_natCast_div_natCast]; norm_cast

theorem two_zpow_neg (n : ℕ) : (2 : ℚ) ^ (-(n : ℤ)) = ((2 ^ n : ℕ) : ℚ)⁻¹ := by
  rw [zpow_neg, zpow_natCast]; push_cast; rfl

theorem zB_eq (B : ℕ) : zB B = ((2 ^ (B / (3 * cden)) : ℕ) : ℚ)⁻¹ := by
  rw [zB, floor_zB, two_zpow_neg]

theorem uB_eq (B : ℕ) : uB B = ((2 ^ (3 * B / (100 * cden)) : ℕ) : ℚ)⁻¹ := by
  rw [uB, floor_uB, two_zpow_neg]

theorem wB_eq (B : ℕ) : wB B = ((2 ^ (B / (50 * cden ^ 2)) : ℕ) : ℚ)⁻¹ := by
  rw [wB, floor_wB, two_zpow_neg]

/-! ## Two estimates over abstract exponents

The exponents `⌊BC/3⌋`, `⌊3BC/100⌋` are closed natural numbers with about `10^{15770}` bits of
`2^·`; they are only ever handled as variables, so that no checker tries to evaluate
`2^{⌊3BC/100⌋}`. -/

/-- `4 z_B ≤ 1/2` when `⌊BC/3⌋ ≥ 3`. -/
theorem four_inv_le (z : ℕ) (hz : 3 ≤ z) : 4 * ((2 ^ z : ℕ) : ℚ)⁻¹ ≤ 1 / 2 := by
  have h8 : (8 : ℚ) ≤ ((2 ^ z : ℕ) : ℚ) := by
    have : 2 ^ 3 ≤ 2 ^ z := Nat.pow_le_pow_right (by norm_num) hz
    exact_mod_cast this
  have : ((2 ^ z : ℕ) : ℚ)⁻¹ ≤ 1 / 8 := by
    rw [inv_le_comm₀ (by linarith) (by norm_num)]; simpa using h8
  linarith

/-- `η̂ < 3 w_B` when `⌊BC/3⌋ ≥ 3` and `⌊3BC/100⌋ ≥ ⌊BC²/50⌋ + 4`. -/
theorem eta_lt (z u w : ℕ) (hz : 3 ≤ z) (hu : w + 4 ≤ u) :
    3 * ((2 ^ u : ℕ) : ℚ)⁻¹ / (1 - 4 * ((2 ^ z : ℕ) : ℚ)⁻¹) + 2 * ((2 ^ w : ℕ) : ℚ)⁻¹ <
      3 * ((2 ^ w : ℕ) : ℚ)⁻¹ := by
  have h4 := four_inv_le z hz
  have hWpos : (0 : ℚ) < ((2 ^ w : ℕ) : ℚ) := by positivity
  have hu' : ((2 ^ u : ℕ) : ℚ)⁻¹ ≤ ((2 ^ w : ℕ) : ℚ)⁻¹ / 16 := by
    have h1 : ((2 ^ w : ℕ) : ℚ) * 16 ≤ ((2 ^ u : ℕ) : ℚ) := by
      have : 2 ^ w * 2 ^ 4 ≤ 2 ^ u := by
        rw [← pow_add]; exact Nat.pow_le_pow_right (by norm_num) hu
      exact_mod_cast this
    rw [div_eq_mul_inv, ← mul_inv]
    exact inv_anti₀ (by positivity) h1
  have hu0 : (0 : ℚ) ≤ ((2 ^ u : ℕ) : ℚ)⁻¹ := by positivity
  have hfrac : 3 * ((2 ^ u : ℕ) : ℚ)⁻¹ / (1 - 4 * ((2 ^ z : ℕ) : ℚ)⁻¹) ≤
      6 * ((2 ^ u : ℕ) : ℚ)⁻¹ := by
    rw [div_le_iff₀ (by linarith)]
    have : (0 : ℚ) ≤ 4 * ((2 ^ z : ℕ) : ℚ)⁻¹ := by positivity
    nlinarith
  have hWi : (0 : ℚ) < ((2 ^ w : ℕ) : ℚ)⁻¹ := inv_pos.2 hWpos
  linarith

/-- `3 · 2^{-w} < D⁻¹` when `3 D < 2^w`. -/
theorem three_inv_lt (w D : ℕ) (hD : 0 < D) (h : 3 * D < 2 ^ w) :
    3 * ((2 ^ w : ℕ) : ℚ)⁻¹ < ((D : ℚ))⁻¹ := by
  have hD' : (0 : ℚ) < D := by exact_mod_cast hD
  have hW : (0 : ℚ) < ((2 ^ w : ℕ) : ℚ) := by positivity
  have h' : 3 * (D : ℚ) < ((2 ^ w : ℕ) : ℚ) := by exact_mod_cast h
  rw [← div_eq_mul_inv, div_lt_iff₀ hW, inv_mul_eq_div, lt_div_iff₀ hD']
  linarith

/-! ## The kernel facts (natural-number arithmetic, at most about `3·10⁵` bits) -/

theorem w_52386 : 4 ^ 52386 / (50 * cden ^ 2) = 322199 := by decide +kernel
theorem w_52385 : 4 ^ 52385 / (50 * cden ^ 2) = 80549 := by decide +kernel
theorem z_52386 : 3 ≤ 4 ^ 52386 / (3 * cden) := by decide +kernel
theorem u_52386 : 322199 + 4 ≤ 3 * 4 ^ 52386 / (100 * cden) := by decide +kernel
theorem B_52386 : 20 * cden ≤ 4 ^ 52386 := by decide +kernel
theorem mem_target : 3 * (64 * Kmem) ^ 6 < 2 ^ 322199 := by decide +kernel
theorem hist_target : 3 * (64 * Khist) ^ 4 < 2 ^ 322199 := by decide +kernel
theorem mem_target_lower : 2 * 2 ^ 80548 ≤ 2 * (64 * Kmem) ^ 6 := by decide +kernel

/-! ## `k = 52386` passes -/

theorem bsearch_52386 : BSearch 52386 := by
  have ez := zB_eq (4 ^ 52386)
  have eu := uB_eq (4 ^ 52386)
  have ew := wB_eq (4 ^ 52386)
  rw [w_52386] at ew
  have hz3 := z_52386
  have hu4 := u_52386
  generalize 4 ^ 52386 / (3 * cden) = z at ez hz3
  generalize 3 * 4 ^ 52386 / (100 * cden) = u at eu hu4
  refine ⟨by norm_num, ?_, ?_, ?_⟩
  · -- `20/C = 20 cden ≤ B`
    have : (20 : ℚ) / C = ((20 * cden : ℕ) : ℚ) := by
      simp only [C]; push_cast; field_simp
    rw [this]; exact_mod_cast B_52386
  · rw [ez]; have := four_inv_le z hz3; linarith
  · have heta : etaHat (4 ^ 52386) < 3 * ((2 ^ 322199 : ℕ) : ℚ)⁻¹ := by
      unfold etaHat; rw [ez, eu, ew]; exact eta_lt z u 322199 hz3 hu4
    have hm := three_inv_lt 322199 ((64 * Kmem) ^ 6)
      (pow_pos (Nat.mul_pos (by norm_num) Kmem_pos) 6) mem_target
    have hh := three_inv_lt 322199 ((64 * Khist) ^ 4)
      (pow_pos (Nat.mul_pos (by norm_num) Khist_pos) 4) hist_target
    have e1 : (((64 * Kmem) ^ 6 : ℕ) : ℚ) = ((64 * Kmem : ℕ) : ℚ) ^ 6 := Nat.cast_pow _ _
    have e2 : (((64 * Khist) ^ 4 : ℕ) : ℚ) = ((64 * Khist : ℕ) : ℚ) ^ 4 := Nat.cast_pow _ _
    rw [e1] at hm
    rw [e2] at hh
    exact lt_min (heta.trans hm) (heta.trans hh)

/-! ## No smaller `k` passes -/

theorem not_bsearch_of_lt {k : ℕ} (hk : k < 52386) : ¬ BSearch k := by
  rintro ⟨-, -, hz, heta⟩
  have ez := zB_eq (4 ^ k)
  have eu := uB_eq (4 ^ k)
  have ew := wB_eq (4 ^ k)
  -- `⌊BC²/50⌋ ≤ 80549` by monotonicity
  have hwle : 4 ^ k / (50 * cden ^ 2) ≤ 80549 := by
    rw [← w_52385]
    exact Nat.div_le_div_right (Nat.pow_le_pow_right (by norm_num) (by omega))
  generalize 4 ^ k / (3 * cden) = z at ez
  generalize 3 * 4 ^ k / (100 * cden) = u at eu
  generalize 4 ^ k / (50 * cden ^ 2) = w at ew hwle
  have hw : ((2 ^ 80549 : ℕ) : ℚ)⁻¹ ≤ wB (4 ^ k) := by
    rw [ew]
    have : ((2 ^ w : ℕ) : ℚ) ≤ ((2 ^ 80549 : ℕ) : ℚ) := by
      exact_mod_cast Nat.pow_le_pow_right (by norm_num) hwle
    exact inv_anti₀ (by positivity) this
  have hu : 0 < uB (4 ^ k) := by rw [eu]; positivity
  have hfrac : 0 < 3 * uB (4 ^ k) / (1 - 4 * zB (4 ^ k)) := div_pos (by linarith) (by linarith)
  have heta' : 2 * ((2 ^ 80549 : ℕ) : ℚ)⁻¹ < etaHat (4 ^ k) := by unfold etaHat; linarith
  have hlow : (((64 * Kmem : ℕ) : ℚ) ^ 6)⁻¹ ≤ 2 * ((2 ^ 80549 : ℕ) : ℚ)⁻¹ := by
    have h1 : ((2 * 2 ^ 80548 : ℕ) : ℚ) ≤ ((2 * (64 * Kmem) ^ 6 : ℕ) : ℚ) := by
      exact_mod_cast mem_target_lower
    have e : 2 ^ 80549 = 2 * 2 ^ 80548 := by rw [pow_succ']
    rw [e]
    push_cast at h1 ⊢
    have hk : (0 : ℚ) < ((64 : ℚ) * Kmem) ^ 6 := by
      have : (0 : ℚ) < Kmem := by exact_mod_cast Kmem_pos
      positivity
    have h2 : (2 : ℚ) ^ 80548 ≤ ((64 : ℚ) * Kmem) ^ 6 := by linarith
    have h3 : (((64 : ℚ) * Kmem) ^ 6)⁻¹ ≤ ((2 : ℚ) ^ 80548)⁻¹ := inv_anti₀ (by positivity) h2
    rw [mul_inv, ← mul_assoc, mul_inv_cancel₀ (by norm_num), one_mul]
    exact h3
  have := heta.trans_le (min_le_left _ _)
  linarith

/-! ## The least `k` -/

theorem exists_bsearch : ∃ k, BSearch k := ⟨52386, bsearch_52386⟩

/-- (25): the least `k ≥ 1` passing the search, as printed (`Nat.find` with classical
decidability). -/
noncomputable def kParam : ℕ := @Nat.find BSearch (Classical.decPred _) exists_bsearch

theorem bsearch_kParam : BSearch kParam := @Nat.find_spec BSearch (Classical.decPred _) exists_bsearch

/-- The Scale paragraph: `k = 52386`. -/
theorem kParam_eq : kParam = 52386 := by
  unfold kParam
  exact (@Nat.find_eq_iff _ _ (Classical.decPred _) exists_bsearch).2
    ⟨bsearch_52386, fun n hn => not_bsearch_of_lt hn⟩

end UND.Param
