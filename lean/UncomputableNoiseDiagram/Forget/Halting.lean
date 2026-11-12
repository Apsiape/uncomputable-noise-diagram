/-
# The halting branch of Theorem 9.3 (Lemma 8.4 for the automaton)

Nodes F4 and Q5 of `BLUEPRINT.md` (Part A.8, A.9), NEW.

Paper (Theorem 9.3, proof): "Halting gives Lemmas 8.4 and 8.5." Prop 9.2: "The historical
statistical base is below `1/64` by (25). Its other base is at most `K_hist C^{6/11}(64K_hist)^{-9}
< 1/64`. Finally, since `ε ≤ 1` and `M ≥ 1`, `K_rare(N₀ε^M)^{1/16} ≤ N₀^{1/16}/(64(N₀+1)) < 1/64`."

Formalization (kernel discipline D13 and the s9 pattern: the halting branch is proved for
`theCAOf U n₀ k s` with variable `n₀`, `k`, `s` (`halting_branch_gen`), then instantiated once):
* **`gateOracle_theCA`**: Prop 4.3's halting branch (`halting_gate`) is the gate oracle of
  Lemma 8.2 for the chart data of `P`, critical depths `a - 1` and `a`;
* **`gate_bounds_final`** (Lemma 6.2 at a single critical gate, `ρ_B ≤ η̂_B`): the short event at
  depth `a - 1` and the long event over `W` have probability at most `η̂_B` on every window;
* `Khist_facts` (`(2(36q)²)^{50} ≤ K_hist`, `q ≤ K_hist`);
* **`halting_branch`**: for every machine `U`, `n ≥ 1`, `ε ∈ I_n`, if `U` halts on `n` then almost
  surely any two complete trajectories of `theCA U` agree at time `0` (Lemma 8.4, the hypothesis
  of `theoremA_of_halting`).
-/
import UncomputableNoiseDiagram.Forget.Coupling
import UncomputableNoiseDiagram.Forget.Gate
import UncomputableNoiseDiagram.Sensors.Selected

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UND.Forget

open UND.Rule UND.Sensors UND.Chart UND.Param UPD
open FNE (Plane)

/-- **The gate oracle of the automaton** (Prop 4.3, halting branch; every phase). -/
theorem gateOracle_theCA {U : Machine} {n0 n k : ℕ} (hn : 1 ≤ n) (hn0 : 1 ≤ n0)
    (hk : k + 1 ≤ n + n0) (hU : U.HaltsOn n) :
    GateOracle (chartData (contentP U n0) k) (n + n0 - 1) (n + n0) := by
  intro c hc
  obtain ⟨ξ, hb, d, hd, hph, hend, hrow, horig⟩ := halting_gate hc hn hn0 hk hU
  refine ⟨ξ, hb, hph, hend, hrow, ?_⟩
  rcases hd with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · simpa using horig
  · simpa using horig

/-- `(2(36q)²)^{50} ≤ K_hist`, `q ≤ K_hist`, `1 ≤ K_hist` (no evaluation of `K_hist`). -/
theorem Khist_facts : (2 * (36 * q) ^ 2) ^ 50 ≤ Khist ∧ q ≤ Khist ∧ 1 ≤ Khist := by
  have hD : 36 * q ≤ Delta := by rw [Delta_eq]; norm_num [q, K]
  have h1 : 2 * (36 * q) ^ 2 ≤ 2 * Delta ^ 2 :=
    Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hD 2)
  have h2 : 1 ≤ 2 * Delta ^ 2 := by
    have := Delta_pos
    have : 1 ≤ Delta ^ 2 := Nat.one_le_pow _ _ this
    omega
  have h3 : (2 * (36 * q) ^ 2) ^ 50 ≤ (2 * Delta ^ 2) ^ 100 :=
    (Nat.pow_le_pow_left h1 50).trans (Nat.pow_le_pow_right h2 (by norm_num))
  have h4 : (2 * Delta ^ 2) ^ 100 ≤ Khist := by
    unfold Khist
    exact Nat.le_mul_of_pos_left _ (Nat.mul_pos (by norm_num) (pow_pos (by norm_num) _))
  have hq1 : q ≤ 2 * (36 * q) ^ 2 := by norm_num [q, K]
  have hq2 : 2 * (36 * q) ^ 2 ≤ (2 * (36 * q) ^ 2) ^ 50 := Nat.le_self_pow (by norm_num) _
  refine ⟨h3.trans h4, hq1.trans (hq2.trans (h3.trans h4)), ?_⟩
  exact Khist_pos

/-- **The halting branch for `theCAOf U n₀ k s`** (variables `n₀`, `k`, `s`): Lemma 8.2 from the
gate oracle, the single-gate bounds and the history bases, then Lemma 8.4. -/
theorem halting_branch_gen (U : Machine) {n0 k s n : ℕ} (hn : 1 ≤ n) (hn0 : 1 ≤ n0)
    (hk : k + 1 ≤ n + n0) (hU : U.HaltsOn n) {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) {W : ℕ}
    (hd0 : UND.Windows.ell (n + n0 - 1) ≤ W) (hd1 : W < UND.Windows.ell (n + n0))
    (hWε : (W : ℝ) * ε ≤ 1) (ρ : ℝ≥0∞)
    (hshort : ∀ c y Q t, pLaw (proposal (CD := chartData (contentP U n0) k) s) (nbhdP (4 ^ k)) ε
      (ShortBad (chartData (contentP U n0) k) s c y Q t (UND.Windows.ell (n + n0 - 1))) ≤ ρ)
    (hlong : ∀ c y Q t, pLaw (proposal (CD := chartData (contentP U n0) k) s) (nbhdP (4 ^ k)) ε
      (LongBad (chartData (contentP U n0) k) s c y Q t W) ≤ ρ)
    (hρ : ρ ≤ ENNReal.ofReal (((64 * Khist : ℕ) : ℝ)⁻¹) ^ 4)
    (hεh : ε ≤ ((((64 * Khist : ℕ) : ℝ) ^ 44)⁻¹))
    (hK : (KrareOf (4 ^ k) : ℝ) * ε < 1) :
    ∀ᵐ ω ∂((theCAOf U n0 k s).noiseLaw₂ ε), ∀ X Y : ℤ → (theCAOf U n0 k s).Config,
      (theCAOf U n0 k s).IsComplete ω X → (theCAOf U n0 k s).IsComplete ω Y → X 0 = Y 0 := by
  have hB : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  obtain ⟨hXK, hqK, hK1⟩ := Khist_facts
  have hβ := hist_base h0 hK1 hXK hqK hεh hWε
  have he4 : (√√ε) ^ 4 = ε := (sqrt_sqrt_facts h0.le zero_le_one (by simpa using h1)).1
  have heγ : ENNReal.ofReal ε ≤ ENNReal.ofReal (√√ε) ^ 4 := by
    rw [← ENNReal.ofReal_pow (Real.sqrt_nonneg _), he4]
  have hno := no_ul_generic (CD := chartData (contentP U n0) k) hB s h0 h1 hd0 hd1
    (gateOracle_theCA hn hn0 hk hU) ρ (ENNReal.ofReal (((64 * Khist : ℕ) : ℝ)⁻¹))
    (ENNReal.ofReal (√√ε)) _ hshort hlong hρ heγ le_rfl hβ
  exact coupling_generic (CD := chartData (contentP U n0) k) hB s h0.le h1 hK hno

/-- **Lemma 6.2 at a single critical gate** (`ρ_B ≤ η̂_B`), at the selected parameters: on every
window, the short event at depth `a - 1` and the long event over the recent `W` atoms have
probability at most `η̂_B`, for any chart data with `B = 4^k` lanes and any rule. -/
theorem gate_bounds_final {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : ε ∈ UND.window loF hiF n)
    {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData (4 ^ kParam) τ}
    (G : (ISite → PhysSym CD) → (ISite → PhysSym CD)) (N : Finset ISite)
    (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ) :
    pLaw G N ε (ShortBad CD sParam c y Q t (UND.Windows.ell (n + n0Param - 1))) ≤
        ENNReal.ofReal ((etaHat (4 ^ kParam) : ℚ) : ℝ) ∧
      pLaw G N ε (LongBad CD sParam c y Q t ⌊(C : ℝ) / ε⌋₊) ≤
        ENNReal.ofReal ((etaHat (4 ^ kParam) : ℚ) : ℝ) := by
  have hR := regime_final hn hε
  have hμ := isProbabilityMeasure_pLaw G N hR.eps_nonneg hR.eps_le
  have hz : 4 * (2 : ℝ) ^ (-⌊((4 ^ kParam : ℕ) : ℝ) * (C : ℝ) / 3⌋) < 1 := by
    rw [← zB_cast]
    exact_mod_cast bsearch_kParam.2.2.1
  have heta := etaHat_cast (4 ^ kParam)
  rw [uB_cast, zB_cast, wB_cast] at heta
  set u : ℝ := (2 : ℝ) ^ (-⌊3 * ((4 ^ kParam : ℕ) : ℝ) * (C : ℝ) / 100⌋) with hu
  set z : ℝ := (2 : ℝ) ^ (-⌊((4 ^ kParam : ℕ) : ℝ) * (C : ℝ) / 3⌋) with hz'
  set w : ℝ := (2 : ℝ) ^ (-⌊((4 ^ kParam : ℕ) : ℝ) * (C : ℝ) ^ 2 / 50⌋) with hw
  have hu0 : 0 ≤ u := by positivity
  have hz0 : 0 ≤ z := by positivity
  have hw0 : 0 ≤ w := by positivity
  have h1z : 0 < 1 - 4 * z := by linarith
  have hu_le : u ≤ ((etaHat (4 ^ kParam) : ℚ) : ℝ) := by
    rw [heta]
    have : u ≤ 3 * u / (1 - 4 * z) := by rw [le_div_iff₀ h1z]; nlinarith
    linarith
  have hw_le : w ≤ ((etaHat (4 ^ kParam) : ℚ) : ℝ) := by
    rw [heta]
    have : 0 ≤ 3 * u / (1 - 4 * z) := div_nonneg (by positivity) h1z.le
    linarith
  have hofReal : ∀ A : Set (PNoise CD), pLaw G N ε A = ENNReal.ofReal ((pLaw G N ε).real A) :=
    fun A => (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
  constructor
  · rw [hofReal]
    refine ENNReal.ofReal_le_ofReal ?_
    have ha := hR.a_ge
    have hp : 99 / 100 * (1 - (1 - ε) ^ UND.Windows.ell (n + n0Param - 1)) ≤
        53 / 100 * (C : ℝ) * (4 : ℝ)⁻¹ ^ 0 := by
      have h1 := upper_mean_le hR.eps_nonneg hR.eps_le (UND.Windows.ell (n + n0Param - 1))
      have h2 := short_support_lt hR.C_pos hR.eps_nonneg hR.a_ge (r := 0) (by omega) hR.eps_lt
      rw [Nat.sub_zero] at h2
      linarith
    have hs := shortBad_le G N hR.eps_nonneg hR.eps_le hR.C_pos 0 _ hp hR.s_ge c y Q t
    rw [pow_zero, mul_one] at hs
    exact hs.trans hu_le
  · rw [hofReal]
    refine ENNReal.ofReal_le_ofReal ?_
    have hs := longBad_le G N hR.eps_nonneg hR.eps_le hR.C_pos ⌊(C : ℝ) / ε⌋₊
      (lower_law_gt hR.C_pos hR.C_le hR.eps_le hR.epsW_ge).le hR.s_le c y Q t
    exact hs.trans hw_le

/-- `ρ_B ≤ η̂_B < (64 K_hist)^{-4}` (the search (25)). -/
theorem eta_final : ENNReal.ofReal ((etaHat (4 ^ kParam) : ℚ) : ℝ) ≤
    ENNReal.ofReal (((64 * Khist : ℕ) : ℝ)⁻¹) ^ 4 := by
  have h := (lt_of_lt_of_le bsearch_kParam.2.2.2 (min_le_right _ _)).le
  generalize etaHat (4 ^ kParam) = η at h
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  rw [← ENNReal.ofReal_pow (by positivity)]
  refine ENNReal.ofReal_le_ofReal (h'.trans (le_of_eq ?_))
  push_cast
  rw [inv_pow]

/-- On every window, `ε ≤ ε_* ≤ (64 K_hist)^{-44}`. -/
theorem eps_hist_final {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : ε ∈ UND.window loF hiF n) :
    ε ≤ ((((64 * Khist : ℕ) : ℝ) ^ 44)⁻¹) := by
  have hlt := (window_subset hn hε).2
  have h := epsStar_le_hist
  generalize epsStar = es at h hlt
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h' ⊢
  exact hlt.le.trans h'

/-- `K ε < 1` from `0 < ε < e ≤ [64K(N+1)]^{-16}`, `K ≥ 1` (variables, D13). -/
theorem rare_of (Kr N : ℕ) (hKr1 : 1 ≤ Kr) (es : ℚ)
    (h : es ≤ (((64 * Kr * (N + 1) : ℕ) : ℚ) ^ 16)⁻¹) {ε : ℝ} (hlt : ε < (es : ℝ)) :
    (Kr : ℝ) * ε < 1 := by
  have hMn : 64 * Kr ≤ 64 * Kr * (N + 1) := Nat.le_mul_of_pos_right _ (Nat.succ_pos N)
  have h' := (Rat.cast_le (K := ℝ)).mpr h
  push_cast at h'
  set M : ℝ := 64 * (Kr : ℝ) * ((N : ℝ) + 1) with hM
  have hM1 : 64 * (Kr : ℝ) ≤ M := by
    have := (Nat.cast_le (α := ℝ)).mpr hMn
    push_cast at this
    rw [hM]
    exact this
  have hKr : (1 : ℝ) ≤ Kr := by exact_mod_cast hKr1
  have hM0 : 1 ≤ M := by linarith
  have hM16 : M ≤ M ^ 16 := le_self_pow₀ hM0 (by norm_num)
  have hεM : ε ≤ M⁻¹ := hlt.le.trans (h'.trans (inv_anti₀ (by positivity) hM16))
  calc (Kr : ℝ) * ε ≤ (Kr : ℝ) * M⁻¹ := by
        rcases le_or_gt 0 ε with hε0 | hε0
        · gcongr
        · nlinarith [inv_pos.mpr (show (0 : ℝ) < M by linarith)]
    _ ≤ (Kr : ℝ) * (64 * (Kr : ℝ))⁻¹ := by gcongr
    _ = 1 / 64 := by field_simp
    _ < 1 := by norm_num

/-- On every window, `K_rare ε < 1` (from `ε < ε_* ≤ [64K_rare(N₀+1)]^{-16}`). -/
theorem rare_final {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : ε ∈ UND.window loF hiF n) :
    (KrareOf Bparam : ℝ) * ε < 1 :=
  rare_of (KrareOf Bparam) N0 (KrareOf_pos Bparam) epsStar (epsStarOf_le_rare Bparam N0)
    (window_subset hn hε).2

/-- **The halting branch of Theorem 9.3** (Lemma 8.4 for the automaton of Theorem A): for every
machine `U`, every `n ≥ 1` with `U` halting on `n` and every `ε ∈ I_n`, almost surely any two
complete trajectories of `theCA U` driven by the same noise agree at time `0`. -/
theorem halting_branch (U : Machine) (n : ℕ) (hn : 1 ≤ n) (ε : ℝ)
    (hε : ε ∈ UND.window loF hiF n) (hU : U.HaltsOn n) :
    ∀ᵐ ω ∂((theCA U).noiseLaw₂ ε), ∀ X Y : ℤ → (theCA U).Config,
      (theCA U).IsComplete ω X → (theCA U).IsComplete ω Y → X 0 = Y 0 := by
  have hR := regime_final hn hε
  have hI := window_subset hn hε
  have ha := a_ge hn
  have hn0 := n0Param_ge
  have hW2 := hR.W_le
  have hell := UND.Windows.ell_pos (n + n0Param)
  have hd0 : UND.Windows.ell (n + n0Param - 1) ≤ ⌊(C : ℝ) / ε⌋₊ := hR.ell_lt.le
  have hd1 : ⌊(C : ℝ) / ε⌋₊ < UND.Windows.ell (n + n0Param) := by omega
  have hWε : (⌊(C : ℝ) / ε⌋₊ : ℝ) * ε ≤ 1 := by
    have := hR.epsW_le
    have := hR.C_le
    linarith
  exact halting_branch_gen U hn (by omega) (by omega) hU hI.1 hR.eps_le hd0 hd1 hWε _
    (fun c y Q t => (gate_bounds_final (CD := chartData (contentP U n0Param) kParam) hn hε
      (proposal sParam) (nbhdP (4 ^ kParam)) c y Q t).1)
    (fun c y Q t => (gate_bounds_final (CD := chartData (contentP U n0Param) kParam) hn hε
      (proposal sParam) (nbhdP (4 ^ kParam)) c y Q t).2)
    eta_final (eps_hist_final hn hε) (Bparam_eq ▸ rare_final hn hε)

end UND.Forget
