/-
# Lemma 6.2 (intrinsic tails), the probabilistic core (N3)

Node N3 of `BLUEPRINT.md` (Part A.6), NEW (Mathlib: `ProbabilityTheory.measure_ge_le_exp_mul_mgf`,
`iIndepFun.mgf_sum`, `measure_sum_ge_le_of_iIndepFun`, `hasSubgaussianMGF_of_mem_Icc`).

Paper (Lemma 6.2, proof): "For independent Bernoulli variables of mean at most
`p_r = .53C4^{-r}`, the exponential moment inequality `1 - p + pe^ϑ ≤ exp(p(e^ϑ - 1))` and the
Chernoff method give `P{at least Bθ successes} ≤ exp[-B(θ log(θ/p_r) - θ + p_r)]`, `θ = .75C`. This
derivation also applies to the higher integer threshold `s`. At `r = 0` its exponent exceeds
`.03BC`: `log(75/53) ≥ 2(75-53)/(75+53) = 11/32` and `.75(11/32) - .22 > .03`. The exponent
increases by at least `BC/3` per rank step because `.75 log 4 - .3975 > 1/3`. … The sum is at most
`3u_B/(1 - 4z_B)`, using `e^{-x} ≤ 2^{-⌊x⌋}`. For a long ruler, `εW ≥ C - ε ≥ .99C`, so (15) gives
`p_W ≥ .98(1 - e^{-.99C}) > .9C`. … Also `s/B ≤ .75C + 1/B ≤ .8C`. Hoeffding's inequality gives
the lower-tail bound `e^{-2B(.1C)²} = e^{-BC²/50}`."

This file proves these steps for abstract independent `{0,1}`-valued random variables (the lane
success indicators of Section 6 are such variables; the geometry that makes them independent is
Lemma 6.1):
* `mgf_le_of_zero_one` (`1 - p + pe^t ≤ exp(p(e^t - 1))`), **`chernoff_zero_one`**,
  **`chernoff_ratio`** (`t = log(θ/p)`: `exp[-n(θ log(θ/p) - θ + p)]`);
* the numerics `log_75_53` (`log(75/53) ≥ 11/32`, from a Taylor bound for `exp`), `log_four_gt`,
  `short_exponent` (`θ log(θ/p_r) - θ + p_r ≥ .03C + rC/3`), `exp_neg_le_two_zpow`
  (`e^{-x} ≤ 2^{-⌊x⌋}`), **`short_tail`** (`P{≥ s successes} ≤ 2^{-⌊3BC/100⌋}(2^{-⌊BC/3⌋})^r`);
* **`hoeffding_zero_one`** (lower tail), **`long_tail`** (`P{< s successes} ≤ 2^{-⌊BC²/50⌋}`);
* `geom_three_le` (`Σ_r 3·4^r u z^r ≤ 3u/(1 - 4z)`), `lower_law_gt` (`.98(1 - (1-ε)^W) > .9C`),
  `short_support_lt` (`ε(ℓ_d + 1) < .53C4^{-r}`).
-/
import UncomputableNoiseDiagram.Parameters.Threshold
import UncomputableNoiseDiagram.Windows
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped NNReal

namespace UND.Sensors

/-! ## Chernoff for independent `{0,1}` variables -/

section Chernoff

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

theorem integrable_of_zero_one [IsProbabilityMeasure μ] {X : Ω → ℝ} (hm : Measurable X)
    (h01 : ∀ ω, X ω = 0 ∨ X ω = 1) : Integrable X μ :=
  Integrable.of_mem_Icc 0 1 hm.aemeasurable
    (ae_of_all _ fun ω => by rcases h01 ω with h | h <;> simp [h])

/-- `E[e^{tX}] = 1 + (e^t - 1)E[X] ≤ exp(p(e^t - 1))` for a `{0,1}` variable of mean `≤ p`,
`t ≥ 0`. -/
theorem mgf_le_of_zero_one [IsProbabilityMeasure μ] {X : Ω → ℝ} (hm : Measurable X)
    (h01 : ∀ ω, X ω = 0 ∨ X ω = 1) {p t : ℝ} (ht : 0 ≤ t) (hp : μ[X] ≤ p) :
    mgf X μ t ≤ exp (p * (exp t - 1)) := by
  have key : ∀ ω, exp (t * X ω) = 1 + (exp t - 1) * X ω := by
    intro ω
    rcases h01 ω with h | h <;> simp [h]
  have hint := integrable_of_zero_one (μ := μ) hm h01
  have e : mgf X μ t = 1 + (exp t - 1) * μ[X] := by
    unfold mgf
    simp_rw [key]
    rw [integral_add (integrable_const 1) (hint.const_mul _), integral_const_mul]
    simp
  rw [e]
  have h1 : 0 ≤ exp t - 1 := by linarith [Real.add_one_le_exp t]
  have h2 := Real.add_one_le_exp (p * (exp t - 1))
  nlinarith

/-- **Chernoff** for independent `{0,1}` variables of means `≤ p`:
`P{a ≤ Σ X_i} ≤ exp(-ta + n p(e^t - 1))`, `t ≥ 0`, `n = |s|`. -/
theorem chernoff_zero_one {ι : Type*} {X : ι → Ω → ℝ} (hind : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (s : Finset ι) {p : ℝ}
    (hp : ∀ i ∈ s, μ[X i] ≤ p) {t : ℝ} (ht : 0 ≤ t) (a : ℝ) :
    μ.real {ω | a ≤ ∑ i ∈ s, X i ω} ≤ exp (-t * a + s.card * (p * (exp t - 1))) := by
  have : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  have hsm : Measurable (∑ i ∈ s, X i) := by
    convert Finset.measurable_sum s (fun i _ => hm i) using 1
    ext ω
    simp
  have hb : ∀ ω, (∑ i ∈ s, X i) ω ∈ Set.Icc (0 : ℝ) s.card := by
    intro ω
    rw [Finset.sum_apply]
    constructor
    · exact Finset.sum_nonneg (fun i _ => by rcases h01 i ω with h | h <;> simp [h])
    · calc ∑ i ∈ s, X i ω ≤ ∑ _i ∈ s, (1 : ℝ) :=
            Finset.sum_le_sum (fun i _ => by rcases h01 i ω with h | h <;> simp [h])
        _ = s.card := by simp
  have hint : Integrable (fun ω => exp (t * (∑ i ∈ s, X i) ω)) μ := by
    refine Integrable.of_mem_Icc 0 (exp (t * s.card))
      ((measurable_const.mul hsm).exp.aemeasurable) (ae_of_all _ fun ω => ?_)
    refine ⟨(exp_pos _).le, exp_le_exp.mpr ?_⟩
    exact mul_le_mul_of_nonneg_left (hb ω).2 ht
  have h := measure_ge_le_exp_mul_mgf (X := ∑ i ∈ s, X i) (μ := μ) a ht hint
  rw [hind.mgf_sum hm s] at h
  simp only [Finset.sum_apply] at h
  refine h.trans ?_
  have hprod : ∏ i ∈ s, mgf (X i) μ t ≤ ∏ _i ∈ s, exp (p * (exp t - 1)) :=
    Finset.prod_le_prod₀ (fun i _ => mgf_nonneg) (fun i hi => mgf_le_of_zero_one (hm i) (h01 i) ht
      (hp i hi))
  calc exp (-t * a) * ∏ i ∈ s, mgf (X i) μ t ≤ exp (-t * a) * ∏ _i ∈ s, exp (p * (exp t - 1)) :=
        mul_le_mul_of_nonneg_left hprod (exp_pos _).le
    _ = exp (-t * a + s.card * (p * (exp t - 1))) := by
        rw [Finset.prod_const, ← Real.exp_nat_mul, ← Real.exp_add]

/-- **Chernoff at `t = log(θ/p)`**: `P{nθ ≤ Σ X_i} ≤ exp[-n(θ log(θ/p) - θ + p)]` for
`0 < p ≤ θ`. -/
theorem chernoff_ratio {ι : Type*} {X : ι → Ω → ℝ} (hind : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (s : Finset ι) {p θ : ℝ}
    (hp0 : 0 < p) (hpθ : p ≤ θ) (hp : ∀ i ∈ s, μ[X i] ≤ p) :
    μ.real {ω | s.card * θ ≤ ∑ i ∈ s, X i ω} ≤
      exp (-(s.card * (θ * log (θ / p) - θ + p))) := by
  have hθ : 0 < θ := hp0.trans_le hpθ
  have ht : 0 ≤ log (θ / p) := Real.log_nonneg ((one_le_div hp0).mpr hpθ)
  refine (chernoff_zero_one hind hm h01 s hp ht _).trans (le_of_eq ?_)
  congr 1
  rw [Real.exp_log (div_pos hθ hp0)]
  field_simp
  ring

end Chernoff

/-! ## The numerics of the short tail -/

/-- `log(75/53) ≥ 11/32` (equivalently `exp(11/32) ≤ 75/53`; a degree-five Taylor bound). -/
theorem log_75_53 : (11 / 32 : ℝ) ≤ log (75 / 53) := by
  rw [Real.le_log_iff_exp_le (by norm_num)]
  have h := Real.exp_bound' (x := 11 / 32) (by norm_num) (by norm_num) (n := 5) (by norm_num)
  refine h.trans ?_
  simp only [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial]
  norm_num

/-- `log 4 > 1.38`. -/
theorem log_four_gt : (1.38 : ℝ) < log 4 := by
  have h : log 4 = 2 * log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]
    norm_num
  rw [h]
  have := Real.log_two_gt_d9
  linarith

/-- The short exponent: with `θ = .75C`, `p_r = .53C4^{-r}`,
`θ log(θ/p_r) - θ + p_r ≥ .03C + rC/3`. -/
theorem short_exponent {C : ℝ} (hC : 0 < C) (r : ℕ) :
    3 / 100 * C + r * C / 3 ≤
      3 / 4 * C * log (3 / 4 * C / (53 / 100 * C * (4 : ℝ)⁻¹ ^ r)) - 3 / 4 * C +
        53 / 100 * C * (4 : ℝ)⁻¹ ^ r := by
  have h4 : (0 : ℝ) < (4 : ℝ)⁻¹ ^ r := by positivity
  have e : 3 / 4 * C / (53 / 100 * C * (4 : ℝ)⁻¹ ^ r) = 75 / 53 * 4 ^ r := by
    rw [inv_pow]
    have : (0 : ℝ) < 4 ^ r := by positivity
    field_simp
    ring
  rw [e, Real.log_mul (by norm_num) (by positivity), Real.log_pow]
  have h1 := log_75_53
  have h2 := log_four_gt
  have hr : (0 : ℝ) ≤ r := Nat.cast_nonneg r
  rcases Nat.eq_zero_or_pos r with h0 | hpos
  · subst h0
    simp only [Nat.cast_zero, pow_zero, mul_one, zero_mul, zero_div, add_zero]
    nlinarith
  · have hr1 : (1 : ℝ) ≤ r := by exact_mod_cast hpos
    have : 0 ≤ 53 / 100 * C * (4 : ℝ)⁻¹ ^ r := by positivity
    have h3 : C * (11 / 32) ≤ C * log (75 / 53) := mul_le_mul_of_nonneg_left h1 hC.le
    have h5 : C * r * 1.38 ≤ C * r * log 4 :=
      mul_le_mul_of_nonneg_left h2.le (by positivity)
    have h6 : C * 1 ≤ C * r := mul_le_mul_of_nonneg_left hr1 hC.le
    linarith

/-- `e^{-x} ≤ 2^{-⌊x⌋}` for `x ≥ 0`. -/
theorem exp_neg_le_two_zpow {x : ℝ} (hx : 0 ≤ x) : exp (-x) ≤ (2 : ℝ) ^ (-⌊x⌋) := by
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ⌊x⌋ = n := ⟨⌊x⌋.toNat, (Int.toNat_of_nonneg (Int.floor_nonneg.mpr hx)).symm⟩
  have hnx : (n : ℝ) ≤ x := by
    have := Int.floor_le x
    rw [hn] at this
    exact_mod_cast this
  rw [hn, zpow_neg, zpow_natCast]
  have h2 : (2 : ℝ) ^ n ≤ exp n := by
    rw [← Real.exp_one_pow]
    exact pow_le_pow_left₀ (by norm_num) (by linarith [Real.add_one_le_exp (1 : ℝ)]) n
  calc exp (-x) ≤ exp (-(n : ℝ)) := exp_le_exp.mpr (by linarith)
    _ = (exp n)⁻¹ := by rw [Real.exp_neg]
    _ ≤ ((2 : ℝ) ^ n)⁻¹ := inv_anti₀ (by positivity) h2

/-! ## The short and long tails -/

section Tails

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Lemma 6.2, the short tail.** For independent `{0,1}` variables of means at most
`p_r = .53C4^{-r}` and a threshold `s ≥ .75C n` (`n` variables):
`P{s ≤ Σ X_i} ≤ 2^{-⌊3nC/100⌋}(2^{-⌊nC/3⌋})^r`. -/
theorem short_tail {ι : Type*} {X : ι → Ω → ℝ} (hind : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (S : Finset ι)
    {C : ℝ} (hC : 0 < C) (r : ℕ) (hp : ∀ i ∈ S, μ[X i] ≤ 53 / 100 * C * (4 : ℝ)⁻¹ ^ r)
    {s : ℝ} (hs : 3 / 4 * C * S.card ≤ s) :
    μ.real {ω | s ≤ ∑ i ∈ S, X i ω} ≤
      (2 : ℝ) ^ (-⌊3 * (S.card : ℝ) * C / 100⌋) * ((2 : ℝ) ^ (-⌊(S.card : ℝ) * C / 3⌋)) ^ r := by
  have : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  have h4 : (0 : ℝ) < (4 : ℝ)⁻¹ ^ r := by positivity
  have h41 : (4 : ℝ)⁻¹ ^ r ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hp0 : 0 < 53 / 100 * C * (4 : ℝ)⁻¹ ^ r := by positivity
  have hpθ : 53 / 100 * C * (4 : ℝ)⁻¹ ^ r ≤ 3 / 4 * C := by nlinarith
  have hn : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have hsub : {ω | s ≤ ∑ i ∈ S, X i ω} ⊆ {ω | S.card * (3 / 4 * C) ≤ ∑ i ∈ S, X i ω} := by
    intro ω hω
    show S.card * (3 / 4 * C) ≤ ∑ i ∈ S, X i ω
    have : s ≤ ∑ i ∈ S, X i ω := hω
    linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans ?_
  refine (chernoff_ratio hind hm h01 S hp0 hpθ hp).trans ?_
  have hexp := short_exponent hC r
  have h1 : exp (-(S.card * (3 / 4 * C * log (3 / 4 * C / (53 / 100 * C * (4 : ℝ)⁻¹ ^ r)) -
      3 / 4 * C + 53 / 100 * C * (4 : ℝ)⁻¹ ^ r))) ≤
      exp (-(3 * (S.card : ℝ) * C / 100)) * exp (-((S.card : ℝ) * C / 3)) ^ r := by
    rw [← Real.exp_nat_mul, ← Real.exp_add]
    refine exp_le_exp.mpr ?_
    have := mul_le_mul_of_nonneg_left hexp hn
    nlinarith
  refine h1.trans ?_
  have hx1 : (0 : ℝ) ≤ 3 * (S.card : ℝ) * C / 100 := by positivity
  have hx2 : (0 : ℝ) ≤ (S.card : ℝ) * C / 3 := by positivity
  exact mul_le_mul (exp_neg_le_two_zpow hx1)
    (pow_le_pow_left₀ (exp_pos _).le (exp_neg_le_two_zpow hx2) r) (by positivity)
    (by positivity)

/-- **Hoeffding's lower tail** for independent `{0,1}` variables:
`P{Σ X_i < a} ≤ exp(-2(Σ E X_i - a)²/n)` for `a ≤ Σ E X_i`. -/
theorem hoeffding_zero_one {ι : Type*} {X : ι → Ω → ℝ} (hind : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (S : Finset ι) {a : ℝ}
    (ha : a ≤ ∑ i ∈ S, μ[X i]) :
    μ.real {ω | ∑ i ∈ S, X i ω < a} ≤ exp (-2 * (∑ i ∈ S, μ[X i] - a) ^ 2 / S.card) := by
  have : IsProbabilityMeasure μ := hind.isProbabilityMeasure
  set Y : ι → Ω → ℝ := fun i => (fun x => -(x - μ[X i])) ∘ X i with hYdef
  have hindY : iIndepFun Y μ := hind.comp (fun i x => -(x - μ[X i])) (fun i => by fun_prop)
  have hY : ∀ i ∈ S, HasSubgaussianMGF (Y i) ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2) μ := by
    intro i _
    have h := (hasSubgaussianMGF_of_mem_Icc (μ := μ) (a := 0) (b := 1) (hm i).aemeasurable
      (ae_of_all _ fun ω => by rcases h01 i ω with h | h <;> simp [h])).neg
    convert h using 1
    funext ω
    simp [hYdef]
  have hε : 0 ≤ ∑ i ∈ S, μ[X i] - a := by linarith
  have hH := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindY (c := fun _ => (‖(1 : ℝ) - 0‖₊ / 2) ^ 2)
    (s := S) hY hε
  have hsub : {ω | ∑ i ∈ S, X i ω < a} ⊆
      {ω | ∑ i ∈ S, μ[X i] - a ≤ ∑ i ∈ S, Y i ω} := by
    intro ω hω
    have h1 : ∑ i ∈ S, X i ω < a := hω
    show ∑ i ∈ S, μ[X i] - a ≤ ∑ i ∈ S, Y i ω
    have e : ∑ i ∈ S, Y i ω = ∑ i ∈ S, μ[X i] - ∑ i ∈ S, X i ω := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [hYdef]
    rw [e]
    linarith
  refine (measureReal_mono hsub (measure_ne_top _ _)).trans (hH.trans (le_of_eq ?_))
  congr 1
  have hc : ((‖(1 : ℝ) - 0‖₊ / 2) ^ 2 : ℝ≥0) = 1 / 4 := by
    rw [sub_zero, nnnorm_one]
    norm_num
  simp only [hc, Finset.sum_const, nsmul_eq_mul]
  push_cast
  rcases Nat.eq_zero_or_pos S.card with h0 | h0
  · simp [h0]
  · have : (0 : ℝ) < S.card := by exact_mod_cast h0
    field_simp
    ring

/-- **Lemma 6.2, the long tail.** For independent `{0,1}` variables of means at least `.9C` and a
threshold `s ≤ .8C n`: `P{Σ X_i < s} ≤ e^{-nC²/50} ≤ 2^{-⌊nC²/50⌋}`. -/
theorem long_tail {ι : Type*} {X : ι → Ω → ℝ} (hind : iIndepFun X μ)
    (hm : ∀ i, Measurable (X i)) (h01 : ∀ i ω, X i ω = 0 ∨ X i ω = 1) (S : Finset ι)
    {C : ℝ} (hC : 0 < C) (hq : ∀ i ∈ S, 9 / 10 * C ≤ μ[X i]) {s : ℝ}
    (hs : s ≤ 8 / 10 * C * S.card) :
    μ.real {ω | ∑ i ∈ S, X i ω < s} ≤ (2 : ℝ) ^ (-⌊(S.card : ℝ) * C ^ 2 / 50⌋) := by
  have hsum : 9 / 10 * C * S.card ≤ ∑ i ∈ S, μ[X i] := by
    calc 9 / 10 * C * S.card = ∑ _i ∈ S, 9 / 10 * C := by
          rw [Finset.sum_const, nsmul_eq_mul]; ring
      _ ≤ ∑ i ∈ S, μ[X i] := Finset.sum_le_sum hq
  have hn : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
  have ha : s ≤ ∑ i ∈ S, μ[X i] := by nlinarith
  refine (hoeffding_zero_one hind hm h01 S ha).trans ?_
  have hx : (0 : ℝ) ≤ (S.card : ℝ) * C ^ 2 / 50 := by positivity
  refine le_trans ?_ (exp_neg_le_two_zpow hx)
  refine exp_le_exp.mpr ?_
  rcases Nat.eq_zero_or_pos S.card with h0 | h0
  · simp [h0]
  · have hpos : (0 : ℝ) < S.card := by exact_mod_cast h0
    have hε : 1 / 10 * C * S.card ≤ ∑ i ∈ S, μ[X i] - s := by nlinarith
    have hε0 : 0 ≤ 1 / 10 * C * S.card := by positivity
    have hsq : (1 / 10 * C * S.card) ^ 2 ≤ (∑ i ∈ S, μ[X i] - s) ^ 2 :=
      pow_le_pow_left₀ hε0 hε 2
    have key : (S.card : ℝ) * C ^ 2 / 50 ≤ 2 * (∑ i ∈ S, μ[X i] - s) ^ 2 / S.card := by
      rw [le_div_iff₀ hpos]
      nlinarith
    calc -2 * (∑ i ∈ S, μ[X i] - s) ^ 2 / S.card =
          -(2 * (∑ i ∈ S, μ[X i] - s) ^ 2 / S.card) := by ring
      _ ≤ -((S.card : ℝ) * C ^ 2 / 50) := neg_le_neg key

end Tails

/-! ## The remaining numerics of Lemma 6.2 -/

/-- `Σ_{r < R} 3·4^r u z^r ≤ 3u/(1 - 4z)` for `0 ≤ 4z < 1`. -/
theorem geom_three_le {u z : ℝ} (hu : 0 ≤ u) (hz : 0 ≤ z) (hz1 : 4 * z < 1) (R : ℕ) :
    ∑ r ∈ Finset.range R, 3 * 4 ^ r * (u * z ^ r) ≤ 3 * u / (1 - 4 * z) := by
  have e : ∑ r ∈ Finset.range R, 3 * 4 ^ r * (u * z ^ r) =
      3 * u * ∑ r ∈ Finset.range R, (4 * z) ^ r := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [mul_pow]
    ring
  rw [e, show 3 * u / (1 - 4 * z) = 3 * u * (1 / (1 - 4 * z)) by ring]
  have h3u : (0 : ℝ) ≤ 3 * u := by positivity
  refine mul_le_mul_of_nonneg_left ?_ h3u
  rw [le_div_iff₀ (by linarith : (0 : ℝ) < 1 - 4 * z), geom_sum_mul_neg]
  have : 0 ≤ (4 * z) ^ R := by positivity
  linarith

/-- (15) at a long ruler: `.98(1 - (1 - ε)^W) > .9C` when `εW ≥ .99C`, `0 < C ≤ .01`. -/
theorem lower_law_gt {C ε : ℝ} {W : ℕ} (hC : 0 < C) (hC1 : C ≤ 1 / 100) (hε1 : ε ≤ 1) (hW : 99 / 100 * C ≤ ε * W) :
    9 / 10 * C < 98 / 100 * (1 - (1 - ε) ^ W) := by
  have h1 : (1 - ε) ^ W ≤ exp (-(ε * W)) := by
    calc (1 - ε) ^ W ≤ exp (-ε) ^ W :=
          pow_le_pow_left₀ (by linarith) (by linarith [Real.add_one_le_exp (-ε)]) W
      _ = exp (-(ε * W)) := by rw [← Real.exp_nat_mul]; ring_nf
  have h2 : exp (-(ε * W)) ≤ exp (-(99 / 100 * C)) := exp_le_exp.mpr (by linarith)
  have h3 : exp (-(99 / 100 * C)) ≤ 1 / (1 + 99 / 100 * C) := by
    rw [Real.exp_neg, one_div]
    exact inv_anti₀ (by positivity) (by linarith [Real.add_one_le_exp (99 / 100 * C)])
  have h4 : 9 / 10 * C < 98 / 100 * (1 - 1 / (1 + 99 / 100 * C)) := by
    have hpos : 0 < 1 + 99 / 100 * C := by positivity
    rw [one_sub_div hpos.ne']
    rw [mul_div_assoc', lt_div_iff₀ hpos]
    nlinarith
  linarith

/-- `((ℓ_d : ℕ) : ℝ) = 2·4^d - 1`. -/
theorem ell_cast (d : ℕ) : ((UND.Windows.ell d : ℕ) : ℝ) = 2 * 4 ^ d - 1 := by
  unfold UND.Windows.ell
  have : 1 ≤ 2 * 4 ^ d := by have := Nat.one_le_pow d 4 (by norm_num); omega
  rw [Nat.cast_sub this]
  push_cast
  ring

/-- The conservative short support bound of Lemma 6.2: for `ε < 21C/(10ℓ_a)`, `a ≥ 3`,
`d = a - 1 - r`, `ε(ℓ_d + 1) < .53C4^{-r}`. -/
theorem short_support_lt {C ε : ℝ} (hC : 0 < C) (hε0 : 0 ≤ ε) {a r : ℕ} (ha : 3 ≤ a)
    (hr : r + 1 ≤ a) (hε : ε < 21 * C / (10 * (UND.Windows.ell a : ℝ))) :
    ε * ((UND.Windows.ell (a - 1 - r) : ℝ) + 1) < 53 / 100 * C * (4 : ℝ)⁻¹ ^ r := by
  obtain ⟨d, rfl⟩ : ∃ d, a = d + r + 1 := ⟨a - 1 - r, by omega⟩
  rw [show d + r + 1 - 1 - r = d by omega, ell_cast]
  rw [ell_cast] at hε
  have h4d : (0 : ℝ) < 4 ^ d := by positivity
  have h4r : (0 : ℝ) < 4 ^ r := by positivity
  have ha' : (4 : ℝ) ^ (d + r + 1) = 4 ^ d * 4 ^ r * 4 := by rw [pow_succ, pow_add]
  have h64 : (64 : ℝ) ≤ 4 ^ (d + r + 1) := by
    calc (64 : ℝ) = 4 ^ 3 := by norm_num
      _ ≤ 4 ^ (d + r + 1) := pow_le_pow_right₀ (by norm_num) ha
  rw [ha'] at hε h64
  have hden : (0 : ℝ) < 10 * (2 * (4 ^ d * 4 ^ r * 4) - 1) := by linarith
  rw [lt_div_iff₀ hden] at hε
  have hprod : 64 * ε ≤ ε * (4 ^ d * 4 ^ r * 4) := by
    have := mul_le_mul_of_nonneg_left h64 hε0
    linarith
  rw [inv_pow, show 2 * (4 : ℝ) ^ d - 1 + 1 = 2 * 4 ^ d by ring]
  have key : ε * (2 * 4 ^ d) * 4 ^ r < 53 / 100 * C := by linarith
  rw [← div_eq_mul_inv, lt_div_iff₀ h4r]
  linarith

/-! ## The bases of Lemma 6.2 -/

/-- `u_B = 2^{-⌊3BC/100⌋}` read in `ℝ`. -/
theorem uB_cast (B : ℕ) :
    ((UND.Param.uB B : ℚ) : ℝ) = (2 : ℝ) ^ (-⌊3 * (B : ℝ) * (UND.Param.C : ℝ) / 100⌋) := by
  unfold UND.Param.uB
  rw [Rat.cast_zpow, Rat.cast_ofNat]
  congr 2
  rw [← Rat.floor_cast (α := ℝ)]
  norm_cast

/-- `z_B = 2^{-⌊BC/3⌋}` read in `ℝ`. -/
theorem zB_cast (B : ℕ) :
    ((UND.Param.zB B : ℚ) : ℝ) = (2 : ℝ) ^ (-⌊(B : ℝ) * (UND.Param.C : ℝ) / 3⌋) := by
  unfold UND.Param.zB
  rw [Rat.cast_zpow, Rat.cast_ofNat]
  congr 2
  rw [← Rat.floor_cast (α := ℝ)]
  norm_cast

/-- `w_B = 2^{-⌊BC²/50⌋}` read in `ℝ`. -/
theorem wB_cast (B : ℕ) :
    ((UND.Param.wB B : ℚ) : ℝ) = (2 : ℝ) ^ (-⌊(B : ℝ) * (UND.Param.C : ℝ) ^ 2 / 50⌋) := by
  unfold UND.Param.wB
  rw [Rat.cast_zpow, Rat.cast_ofNat]
  congr 2
  rw [← Rat.floor_cast (α := ℝ)]
  norm_cast

/-- **Lemma 6.2, the union over a bin**: at most `3·4^r` short gates of rank offset `r`, each bad
with probability at most `u_B z_B^r`, and at most two long gates, each bad with probability at most
`w_B`, give at most `3u_B/(1 - 4z_B) + 2w_B = η̂_B`. -/
theorem eta_bound {u z w : ℝ} (hu : 0 ≤ u) (hz : 0 ≤ z) (hz1 : 4 * z < 1) (hw : 0 ≤ w) (R : ℕ)
    (n : ℕ → ℕ) (hn : ∀ r, n r ≤ 3 * 4 ^ r) (m : ℕ) (hm : m ≤ 2) :
    ∑ r ∈ Finset.range R, (n r : ℝ) * (u * z ^ r) + m * w ≤ 3 * u / (1 - 4 * z) + 2 * w := by
  have h1 : ∑ r ∈ Finset.range R, (n r : ℝ) * (u * z ^ r) ≤
      ∑ r ∈ Finset.range R, 3 * 4 ^ r * (u * z ^ r) := by
    refine Finset.sum_le_sum fun r _ => mul_le_mul_of_nonneg_right ?_ (by positivity)
    exact_mod_cast hn r
  have h2 : (m : ℝ) * w ≤ 2 * w := mul_le_mul_of_nonneg_right (by exact_mod_cast hm) hw
  linarith [geom_three_le hu hz hz1 R]

/-- The selected parameters: `η̂_B` in `ℝ`. -/
theorem etaHat_cast (B : ℕ) :
    ((UND.Param.etaHat B : ℚ) : ℝ) =
      3 * ((UND.Param.uB B : ℚ) : ℝ) / (1 - 4 * ((UND.Param.zB B : ℚ) : ℝ)) +
        2 * ((UND.Param.wB B : ℚ) : ℝ) := by
  unfold UND.Param.etaHat
  push_cast
  ring

end UND.Sensors
