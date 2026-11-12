/-
# Prop 9.2, the history bases (Q5, last clause)

Part of node Q5 of `BLUEPRINT.md` (Part A.9), NEW: the history bases (22) of Lemma 8.2 in the form
consumed by `hpath_null` (`Forget/History.lean`).

Paper (Lemma 8.2): "Since `W ≤ C/ε`, their counted sum has bases `K_hist C^{6/11} ε^{9/44}`,
`K_hist ρ_B^{1/4}`, `3/4 - 6/11 = 9/44 > 0`." Prop 9.2: "The historical statistical base is below
`1/64` by (25). Its other base is at most `K_hist C^{6/11}(64K_hist)^{-9} < 1/64`."

Formalization (kernel discipline D13: `K` stays a variable with `(2(36q)²)^{50} ≤ K`, `q ≤ K`;
instantiated at `K_hist`): with `γ = ε^{1/4}` (`√√ε`), `α = (64K)^{-1}` (so `ρ_B ≤ η̂_B < α⁴` by
(25)), and `Wε ≤ 1`, the block weights of a node,
`qα + Σ_{f ≥ 11} (W + 1)·4(2(36q)²)^{50(f-1)}(175(W + 50(f-1) + 1) + 1)⁴ γ^{3f}`, are below `1`
(**`hist_base`**): each deep term is at most `256·9200⁴ X^{50} γ 2^{-f}` (`term_le`; `(W+1)γ⁴ ≤ 2`,
`(175 gap + 1)γ⁴ ≤ 9200 f`, `f⁴ ≤ 16^f`, `3f - 20 ≥ f`), and `γ ≤ (64K)^{-11}` from
`ε ≤ (64K)^{-44}` (the threshold (27)).
-/
import UncomputableNoiseDiagram.Forget.History
import UncomputableNoiseDiagram.Parameters.Threshold

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open scoped ENNReal

namespace UND.Forget

open UND.Param

/-- `f⁴ ≤ 16^f`. -/
theorem pow_four_le (f : ℕ) : (f : ℝ) ^ 4 ≤ 16 ^ f := by
  have h : (f : ℝ) ≤ 2 ^ f := by exact_mod_cast (Nat.lt_two_pow_self).le
  calc (f : ℝ) ^ 4 ≤ (2 ^ f) ^ 4 := by gcongr
    _ = 16 ^ f := by rw [← pow_mul, mul_comm, pow_mul]; norm_num

/-- **One deep term**: for `f ≥ 11`, `(W+1)·4X^{50(f-1)}(175 gap(f) + 1)⁴ γ^{3f} ≤
256·9200⁴ X^{50} γ 2^{-f}` when `Wγ⁴ ≤ 1`, `γ ≤ 1`, `32 X^{50} γ ≤ 1`. -/
theorem term_le {e : ℝ} (he0 : 0 ≤ e) (he1 : e ≤ 1) {W : ℕ} (hWe : (W : ℝ) * e ^ 4 ≤ 1)
    (X : ℕ) (hX : 1 ≤ X) (h32 : 32 * (X : ℝ) ^ 50 * e ≤ 1) {f : ℕ} (hf : 11 ≤ f) :
    (((W + 1) * (4 * X ^ (50 * (f - 1))) * (175 * gap W f + 1) ^ 4 : ℕ) : ℝ) * e ^ (3 * f) ≤
      256 * 9200 ^ 4 * (X : ℝ) ^ 50 * e * (1 / 2) ^ f := by
  have he4 : e ^ 4 ≤ 1 := pow_le_one₀ he0 he1
  have he40 : 0 ≤ e ^ 4 := by positivity
  have hX1 : (1 : ℝ) ≤ X := by exact_mod_cast hX
  have hf1 : ((f - 1 : ℕ) : ℝ) = (f : ℝ) - 1 := by rw [Nat.cast_sub (by omega)]; simp
  have hfr : (11 : ℝ) ≤ f := by exact_mod_cast hf
  -- `(W + 1) γ⁴ ≤ 2`
  have hA : ((W : ℝ) + 1) * e ^ 4 ≤ 2 := by nlinarith
  -- `(175 gap + 1) γ⁴ ≤ 9200 f`
  have hG : ((175 * gap W f + 1 : ℕ) : ℝ) * e ^ 4 ≤ 9200 * f := by
    simp only [gap]
    push_cast
    rw [hf1]
    nlinarith
  have hG0 : 0 ≤ ((175 * gap W f + 1 : ℕ) : ℝ) * e ^ 4 := by positivity
  -- `X^{50(f-1)} ≤ X^{50 f}`
  have hXp : (X : ℝ) ^ (50 * (f - 1)) ≤ (X : ℝ) ^ (50 * f) :=
    pow_le_pow_right₀ hX1 (by omega)
  -- `γ^{3f} = γ⁴ (γ⁴)⁴ γ^{3f - 20}`, `γ^{3f-20} ≤ γ^f`
  have hsplit : e ^ (3 * f) = e ^ 4 * (e ^ 4) ^ 4 * e ^ (3 * f - 20) := by
    rw [← pow_mul, ← pow_add, ← pow_add]
    congr 1
    omega
  have hrest : e ^ (3 * f - 20) ≤ e ^ f := pow_le_pow_of_le_one he0 he1 (by omega)
  have hrest0 : 0 ≤ e ^ (3 * f - 20) := by positivity
  have hf4 := pow_four_le f
  have hb : (16 * (X : ℝ) ^ 50 * e) ^ f ≤ 32 * (X : ℝ) ^ 50 * e * (1 / 2) ^ f := by
    have h1 : (16 * (X : ℝ) ^ 50 * e) = (32 * (X : ℝ) ^ 50 * e) * (1 / 2) := by ring
    rw [h1, mul_pow]
    gcongr
    calc (32 * (X : ℝ) ^ 50 * e) ^ f ≤ (32 * (X : ℝ) ^ 50 * e) ^ 1 :=
          pow_le_pow_of_le_one (by positivity) h32 (by omega)
      _ = 32 * (X : ℝ) ^ 50 * e := pow_one _
  push_cast
  rw [hsplit]
  calc ((W : ℝ) + 1) * (4 * (X : ℝ) ^ (50 * (f - 1))) * ((175 * (gap W f : ℝ) + 1)) ^ 4 *
        (e ^ 4 * (e ^ 4) ^ 4 * e ^ (3 * f - 20))
      = (((W : ℝ) + 1) * e ^ 4) * (4 * (X : ℝ) ^ (50 * (f - 1))) *
          (((175 * gap W f + 1 : ℕ) : ℝ) * e ^ 4) ^ 4 * e ^ (3 * f - 20) := by
        push_cast; ring
    _ ≤ 2 * (4 * (X : ℝ) ^ (50 * f)) * (9200 * f) ^ 4 * e ^ f := by
        gcongr
    _ = 8 * 9200 ^ 4 * ((f : ℝ) ^ 4 * ((X : ℝ) ^ 50) ^ f * e ^ f) := by
        rw [← pow_mul, mul_comm 50 f]; ring
    _ ≤ 8 * 9200 ^ 4 * (16 ^ f * ((X : ℝ) ^ 50) ^ f * e ^ f) := by gcongr
    _ = 8 * 9200 ^ 4 * (16 * (X : ℝ) ^ 50 * e) ^ f := by rw [mul_pow, mul_pow]
    _ ≤ 8 * 9200 ^ 4 * (32 * (X : ℝ) ^ 50 * e * (1 / 2) ^ f) := by gcongr
    _ = 256 * 9200 ^ 4 * (X : ℝ) ^ 50 * e * (1 / 2) ^ f := by ring

/-- `(√√ε)⁴ = ε` and `√√ε ≤ δ` from `ε ≤ δ⁴` (`δ ≥ 0`). -/
theorem sqrt_sqrt_facts {ε δ : ℝ} (h0 : 0 ≤ ε) (hδ : 0 ≤ δ) (h : ε ≤ δ ^ 4) :
    (√√ε) ^ 4 = ε ∧ √√ε ≤ δ := by
  refine ⟨?_, ?_⟩
  · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, Real.sq_sqrt (Real.sqrt_nonneg _),
      Real.sq_sqrt h0]
  · have h1 : √ε ≤ δ ^ 2 := by
      rw [show δ ^ 4 = (δ ^ 2) ^ 2 by ring] at h
      exact Real.sqrt_le_sqrt h |>.trans (by rw [Real.sqrt_sq (by positivity)])
    exact Real.sqrt_le_sqrt h1 |>.trans (by rw [Real.sqrt_sq hδ])

/-- **The history bases (22)** in the form of `hpath_null`: with `α = (64K)^{-1}`,
`γ = ε^{1/4}`, `ε ≤ (64K)^{-44}`, `Wε ≤ 1` and `(2(36q)²)^{50} ≤ K`, `q ≤ K`, the block weights of
a node sum to less than `1`. -/
theorem hist_base {ε : ℝ} (h0 : 0 < ε) {K : ℕ} (hK : 1 ≤ K)
    (hXK : (2 * (36 * q) ^ 2) ^ 50 ≤ K) (hqK : q ≤ K)
    (hε : ε ≤ ((((64 * K : ℕ) : ℝ) ^ 44)⁻¹)) {W : ℕ} (hW : (W : ℝ) * ε ≤ 1) :
    (q : ℝ≥0∞) * ENNReal.ofReal (((64 * K : ℕ) : ℝ)⁻¹) +
      ∑' f : ℕ, (if 11 ≤ f then (((W + 1) * (4 * (2 * (36 * q) ^ 2) ^ (50 * (f - 1))) *
        (175 * gap W f + 1) ^ 4 : ℕ) : ℝ≥0∞) * ENNReal.ofReal (√√ε) ^ (3 * f) else 0) < 1 := by
  set X : ℕ := 2 * (36 * q) ^ 2 with hXdef
  set k64 : ℝ := ((64 * K : ℕ) : ℝ) with hk64
  have hk1 : (64 : ℝ) ≤ k64 := by
    rw [hk64]; push_cast
    have : (1 : ℝ) ≤ K := by exact_mod_cast hK
    linarith
  have hk0 : 0 < k64 := by linarith
  set δ : ℝ := k64⁻¹ ^ 11 with hδ
  have hδ0 : 0 ≤ δ := by positivity
  have hε' : ε ≤ δ ^ 4 := by
    rw [hδ, ← pow_mul, inv_pow]
    exact hε
  obtain ⟨he4, heδ⟩ := sqrt_sqrt_facts h0.le hδ0 hε'
  set e : ℝ := √√ε with he
  have he0 : 0 ≤ e := Real.sqrt_nonneg _
  have hδ1 : δ ≤ 1 := pow_le_one₀ (by positivity) (inv_le_one_of_one_le₀ (by linarith))
  have he1 : e ≤ 1 := heδ.trans hδ1
  have hX1 : 1 ≤ X := by rw [hXdef]; norm_num [q, UND.Param.K]
  have hXK' : (X : ℝ) ^ 50 ≤ K := by exact_mod_cast hXK
  have hKk : (K : ℝ) ≤ k64 := by rw [hk64]; push_cast; linarith
  -- `X^{50} γ ≤ K (64K)^{-11} ≤ k64^{-10}`
  have hXe : (X : ℝ) ^ 50 * e ≤ k64⁻¹ ^ 10 := by
    calc (X : ℝ) ^ 50 * e ≤ k64 * δ := by gcongr; exact hXK'.trans hKk
      _ = k64⁻¹ ^ 10 := by
        rw [hδ, pow_succ, ← mul_assoc, mul_comm k64, mul_assoc, mul_inv_cancel₀ hk0.ne', mul_one]
  have hX47 : 2 ^ 47 ≤ X := by rw [hXdef]; norm_num [q, UND.Param.K]
  have hK47 : 2 ^ 47 ≤ K := hX47.trans ((Nat.le_self_pow (by norm_num) X).trans hXK)
  have hk53 : (2 : ℝ) ^ 53 ≤ k64 := by
    rw [hk64]; push_cast
    have : ((2 ^ 47 : ℕ) : ℝ) ≤ K := by exact_mod_cast hK47
    push_cast at this
    linarith
  have hk10 : k64⁻¹ ^ 10 ≤ ((2 : ℝ) ^ 53)⁻¹ ^ 10 := by gcongr
  have h32 : 32 * (X : ℝ) ^ 50 * e ≤ 1 := by
    have : (32 : ℝ) * ((2 : ℝ) ^ 53)⁻¹ ^ 10 ≤ 1 := by norm_num
    nlinarith
  have hWe : (W : ℝ) * e ^ 4 ≤ 1 := by rw [he4]; exact hW
  set A : ℝ := 256 * 9200 ^ 4 * (X : ℝ) ^ 50 * e with hA
  have hA0 : 0 ≤ A := by positivity
  have hA1 : 2 * A ≤ 1 / 4 := by
    have : (2 : ℝ) * 256 * 9200 ^ 4 * ((2 : ℝ) ^ 53)⁻¹ ^ 10 ≤ 1 / 4 := by norm_num
    rw [hA]; nlinarith
  -- each term `≤ A 2^{-f}`
  have hterm : ∀ f : ℕ, (if 11 ≤ f then (((W + 1) * (4 * X ^ (50 * (f - 1))) *
      (175 * gap W f + 1) ^ 4 : ℕ) : ℝ≥0∞) * ENNReal.ofReal e ^ (3 * f) else 0) ≤
      ENNReal.ofReal (A * (1 / 2) ^ f) := by
    intro f
    split_ifs with hf
    · rw [← ENNReal.ofReal_natCast, ← ENNReal.ofReal_pow he0, ← ENNReal.ofReal_mul (by positivity)]
      exact ENNReal.ofReal_le_ofReal (term_le he0 he1 hWe X hX1 h32 hf)
    · exact zero_le
  have hsum : Summable fun f : ℕ => A * (1 / 2 : ℝ) ^ f :=
    (summable_geometric_two).mul_left A
  have htsum : ∑' f : ℕ, A * (1 / 2 : ℝ) ^ f = 2 * A := by
    rw [tsum_mul_left, tsum_geometric_two]; ring
  calc (q : ℝ≥0∞) * ENNReal.ofReal k64⁻¹ +
        ∑' f : ℕ, (if 11 ≤ f then (((W + 1) * (4 * X ^ (50 * (f - 1))) *
          (175 * gap W f + 1) ^ 4 : ℕ) : ℝ≥0∞) * ENNReal.ofReal e ^ (3 * f) else 0)
      ≤ ENNReal.ofReal ((q : ℝ) * k64⁻¹) + ∑' f : ℕ, ENNReal.ofReal (A * (1 / 2) ^ f) := by
        gcongr with f
        · rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_natCast]
        · exact hterm f
    _ = ENNReal.ofReal ((q : ℝ) * k64⁻¹ + 2 * A) := by
        rw [← ENNReal.ofReal_tsum_of_nonneg (fun f => by positivity) hsum, htsum,
          ENNReal.ofReal_add (by positivity) (by positivity)]
    _ < 1 := by
        rw [ENNReal.ofReal_lt_one]
        have hq : (q : ℝ) * k64⁻¹ ≤ 1 / 64 := by
          have hqK' : (q : ℝ) ≤ K := by exact_mod_cast hqK
          rw [hk64]; push_cast
          rw [mul_inv_le_iff₀ (by positivity)]
          linarith
        linarith

end UND.Forget
