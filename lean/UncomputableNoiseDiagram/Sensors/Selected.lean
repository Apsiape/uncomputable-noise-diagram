/-
# Section 6 at the selected parameters (N3, N4 with Prop 9.2)

Node N4 of `BLUEPRINT.md` (Part A.6) and the Section 6 clauses of Prop 9.2 (Q5), NEW.

Paper (Section 6, after Lemma 6.1): "For a selected input `n ≥ 1` put `a = n + n₀` and
`I_n = (2C/ℓ_a, 21C/(10ℓ_a))`, `W = ⌊C/ε⌋ (ε ∈ I_n)` (17). The parameters guarantee
`a ≥ k + 3 ≥ 4`, `ε ≤ C/100`, `0 < C < .01`, and `B ≥ 20/C`. In particular `ℓ_{a-1} < W`,
`ℓ_a ≥ 2W` (18)." Lemma 6.2: "Also `s/B ≤ .75C + 1/B ≤ .8C`." Prop 9.2: "`K_mem γ < 1/32`".

Formalization (kernel discipline D13: `kParam`, `cden`, `Kmem` stay symbolic):
* `Bparam_eq` (`B = 4^k`, D24: the kernel unfolds `Bparam` before `HPow.hPow`), `cden_ge`,
  `C_le_hundredth` (`C ≤ 1/100`);
* **`regime_final`**: every `ε ∈ I_n`, `n ≥ 1`, gives the sensor regime with `C`, `a = n + n₀`,
  `W = ⌊C/ε⌋`, `s = ⌈3CB/4⌉`, `B = 4^k`;
* **`joint_source_final`** (Lemma 6.3 at the selected parameters): for the automaton on any chart
  data with `B = 4^k` lanes, `P{R ∪ S at all labels of L} ≤ γ^{|L|}` with
  `γ = gammaOf (4^k) = √C + η̂_B^{1/6}`.
-/
import UncomputableNoiseDiagram.Sensors.Joint
import UncomputableNoiseDiagram.Parameters.Bases

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Real

namespace UND.Sensors

open UND.Param UND.Rule

/-- (25): `B = 4^k` (D24; the kernel unfolds `Bparam` before `HPow.hPow`, so no power of `4` is
evaluated). -/
theorem Bparam_eq : Bparam = 4 ^ kParam := by
  unfold Bparam
  rfl

theorem cden_ge : 100 ≤ cden := by
  have h1 : 128 ≤ 128 * Kmem := Nat.le_mul_of_pos_right 128 Kmem_pos
  have h2 : 128 ^ 2 ≤ (128 * Kmem) ^ 2 := Nat.pow_le_pow_left h1 2
  unfold cden
  omega

/-- `0 < C ≤ 1/100`. -/
theorem C_le_hundredth : (C : ℝ) ≤ 1 / 100 := by
  have h : (100 : ℝ) ≤ cden := by exact_mod_cast cden_ge
  rw [C_eq_inv]
  push_cast
  rw [one_div]
  exact inv_anti₀ (by norm_num) h

theorem C_real_eq : (C : ℝ) = (cden : ℝ)⁻¹ := by
  rw [C_eq_inv]
  push_cast
  rfl

/-- **Section 6 on every window**: `ε ∈ I_n`, `n ≥ 1`, gives the sensor regime with `a = n + n₀`,
`W = ⌊C/ε⌋`, `s = ⌈3CB/4⌉` and `B = 4^k`. -/
theorem regime_final {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : ε ∈ UND.window loF hiF n) :
    Regime (C : ℝ) ε (n + n0Param) ⌊(C : ℝ) / ε⌋₊ sParam (4 ^ kParam) := by
  have hC0 : (0 : ℝ) < C := by exact_mod_cast C_pos
  have hCle := C_le_hundredth
  have hI := window_subset hn hε
  have h100 := le_C_div_100 hn hε
  have hε0 : 0 < ε := hI.1
  have ha := (a_ge hn).2
  obtain ⟨hm1, hm2⟩ := ruler_margins cden n0Param n (n + n0Param - 1) cden_pos (by omega) hε
  rw [← C_real_eq, show n + n0Param - 1 + 1 = n + n0Param by omega] at hm2
  rw [← C_real_eq] at hm1
  have hWle : (⌊(C : ℝ) / ε⌋₊ : ℝ) ≤ C / ε := Nat.floor_le (by positivity)
  have hWgt : (C : ℝ) / ε < ⌊(C : ℝ) / ε⌋₊ + 1 := Nat.lt_floor_add_one _
  have hBC : (20 : ℝ) ≤ C * ((4 ^ kParam : ℕ) : ℝ) := by
    have h := bsearch_kParam.2.1
    have h' : (20 : ℝ) / C ≤ ((4 ^ kParam : ℕ) : ℝ) := by exact_mod_cast h
    rw [div_le_iff₀ hC0] at h'
    linarith
  have hs1 : (3 * C * (Bparam : ℚ) / 4 : ℚ) ≤ (sParam : ℚ) := Nat.le_ceil _
  have hs2 : ((sParam : ℕ) : ℚ) < 3 * C * (Bparam : ℚ) / 4 + 1 :=
    Nat.ceil_lt_add_one (by have := C_pos; positivity)
  rw [Bparam_eq] at hs1 hs2
  have hs1' : ((3 * C * ((4 ^ kParam : ℕ) : ℚ) / 4 : ℚ) : ℝ) ≤ ((sParam : ℕ) : ℝ) := by
    exact_mod_cast hs1
  have hs2' : ((sParam : ℕ) : ℝ) < ((3 * C * ((4 ^ kParam : ℕ) : ℚ) / 4 + 1 : ℚ) : ℝ) := by
    exact_mod_cast hs2
  push_cast at hs1' hs2' hBC
  refine
    { C_pos := hC0
      C_le := hCle
      eps_nonneg := hε0.le
      eps_le := by linarith
      a_ge := by omega
      eps_lt := ?_
      epsW_ge := ?_
      epsW_le := ?_
      ell_lt := hm1
      W_le := hm2.le
      s_ge := by push_cast; linarith
      s_le := by push_cast; linarith }
  · have e : ((hiF n : ℚ) : ℝ) = 21 * (C : ℝ) / (10 * (UND.Windows.ell (n + n0Param) : ℝ)) := by
      rw [C_real_eq]
      unfold hiF UND.Windows.hi
      push_cast
      have h1 : (cden : ℝ) ≠ 0 := by exact_mod_cast cden_pos.ne'
      have h2 : (UND.Windows.ell (n + n0Param) : ℝ) ≠ 0 := by
        exact_mod_cast (UND.Windows.ell_pos _).ne'
      field_simp
    have := hε.2
    rwa [e] at this
  · have h := (div_lt_iff₀ hε0).1 hWgt
    nlinarith
  · have h := (le_div_iff₀ hε0).1 hWle
    linarith

/-- **Lemma 6.3 at the selected parameters**: for the automaton on any chart data with `B = 4^k`
lanes, every `ε ∈ I_n` (`n ≥ 1`), every chart phase `(tc, tr)` and every finite set `L` of source
labels, `P{R ∪ S at all labels of L} ≤ γ^{|L|}`, `γ = √C + η̂_B^{1/6}`. -/
theorem joint_source_final {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData (4 ^ kParam) τ}
    (G : (ISite → PhysSym CD) → (ISite → PhysSym CD)) (N : Finset ISite) {n : ℕ} (hn : 1 ≤ n)
    {ε : ℝ} (hε : ε ∈ UND.window loF hiF n) (tc tr : ℕ → Bool) (L : Finset Label) :
    (pLaw G N ε).real (⋂ l ∈ L, (RawEv CD ⌊(C : ℝ) / ε⌋₊ l ∪
      StatEv CD tc tr kParam sParam (n + n0Param) ⌊(C : ℝ) / ε⌋₊ l)) ≤
      gammaOf (4 ^ kParam) ^ L.card := by
  have hR := regime_final hn hε
  have hz : 4 * (2 : ℝ) ^ (-⌊((4 ^ kParam : ℕ) : ℝ) * (C : ℝ) / 3⌋) < 1 := by
    rw [← zB_cast]
    exact_mod_cast bsearch_kParam.2.2.1
  have heta : ((etaHat (4 ^ kParam) : ℚ) : ℝ) ≤ 1 := by
    have h1 := lt_of_lt_of_le bsearch_kParam.2.2.2 (min_le_left _ _)
    have h2 : ((((64 * Kmem : ℕ) : ℚ) ^ 6)⁻¹ : ℚ) ≤ 1 := by
      have : (1 : ℚ) ≤ ((64 * Kmem : ℕ) : ℚ) ^ 6 := by
        have hk : 1 ≤ 64 * Kmem := Nat.le_mul_of_pos_right 64 Kmem_pos |>.trans' (by norm_num)
        exact one_le_pow₀ (by exact_mod_cast hk)
      exact inv_le_one_of_one_le₀ this
    exact_mod_cast (h1.trans_le h2).le
  rw [etaHat_cast, uB_cast, zB_cast, wB_cast] at heta
  have e : gammaOf (4 ^ kParam) = √(C : ℝ) + (3 * (2 : ℝ) ^ (-⌊3 * ((4 ^ kParam : ℕ) : ℝ) *
      (C : ℝ) / 100⌋) / (1 - 4 * (2 : ℝ) ^ (-⌊((4 ^ kParam : ℕ) : ℝ) * (C : ℝ) / 3⌋)) +
        2 * (2 : ℝ) ^ (-⌊((4 ^ kParam : ℕ) : ℝ) * (C : ℝ) ^ 2 / 50⌋)) ^ ((1 : ℝ) / 6) := by
    unfold gammaOf
    rw [etaHat_cast, uB_cast, zB_cast, wB_cast]
  rw [e]
  exact joint_source_bound G N hR le_rfl hz heta tc tr L

end UND.Sensors
