/-
# The PCA layer, part 6: forgetting implies ergodicity; memory gives two stationary laws

Nodes P6 and P7 of `BLUEPRINT.md` (Part A.1). Ported from the forgetting core
(`FixedNoiseErgodicity/Section2/ForgetErgodic.lean`, same authors, v4.35 version) to an arbitrary
cellular automaton `A : CA d` (decision D3), with two additions used by the main theorem:
memory between two *translation-invariant* initial laws gives two distinct translation-invariant
stationary laws (the last paragraph of the proof of Theorem 7.3), and two distinct stationary laws
exclude ergodicity.

* the mixture formula in real form; `dtv(μΦ^t|_O, νΦ^t|_O) ≤ 2 δ_O(t)` (`dtv_law_le`);
* **`ergodic_of_forgets`**: if the process forgets it is ergodic, and its stationary law `π`
  satisfies `dtv(μΦ^t|_O, π|_O) ≤ 2 δ_O(t)` (used by Lemma 8.5 through `forgets_of_coupling`);
* **`two_stationary_of_memory`** (the forgetting core's `two_invariant_of_memory`, for two initial
  laws) and **`hasTwoTIStationaryLaws_of_memory`** (Theorem 7.3, last paragraph: "The limits from
  bits zero and one are distinct", with the translation invariance of P5);
* `not_ergodic_of_two` (two distinct stationary laws exclude ergodicity).
-/
import UncomputableNoiseDiagram.PCA.Translation

set_option autoImplicit false

noncomputable section

namespace UND.CA

open MeasureTheory Filter Topology
open scoped ENNReal

variable {d : ℕ} (A : CA d)

/-! ## Forgetting implies ergodicity -/

/-- `x ↦ P_x(X_t ∈ B)` is measurable. -/
theorem measurable_law_dirac_apply {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (t : ℕ)
    {B : Set A.Config} (hB : MeasurableSet B) :
    Measurable (fun x : A.Config => A.law ε (Measure.dirac x) t B) := by
  have := A.isProbabilityMeasure_noiseLaw h0 h1
  have hS : MeasurableSet ((fun p : A.Config × A.Noise => A.run p.1 p.2 t) ⁻¹' B) :=
    A.measurable_run t hB
  have hfun : (fun x : A.Config => A.law ε (Measure.dirac x) t B) =
      fun x => A.noiseLaw ε (Prod.mk x ⁻¹' ((fun p : A.Config × A.Noise =>
        A.run p.1 p.2 t) ⁻¹' B)) := by
    funext x
    have hm : Measurable (fun ω : A.Noise => A.run x ω t) :=
      (A.measurable_run t).comp measurable_prodMk_left
    rw [A.law_dirac h0 h1, Measure.map_apply hm hB]
    rfl
  rw [hfun]
  exact measurable_measure_prodMk_left hS

/-- The mixture formula in real form. -/
theorem law_toReal_eq_integral {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure A.Config)
    [IsProbabilityMeasure μ] (t : ℕ) {B : Set A.Config} (hB : MeasurableSet B) :
    (A.law ε μ t B).toReal = ∫ x, (A.law ε (Measure.dirac x) t B).toReal ∂μ := by
  rw [A.law_apply_eq_lintegral h0 h1 μ t hB, integral_toReal
    (A.measurable_law_dirac_apply h0 h1 t hB).aemeasurable
    (Eventually.of_forall (fun x => by
      have := A.isProbabilityMeasure_law h0 h1 (Measure.dirac x) t
      exact measure_lt_top _ _))]

/-- From any initial law, the window probabilities stay within `δ_O(t)` of those from `0`. -/
theorem abs_law_sub_zero_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure A.Config)
    [IsProbabilityMeasure μ] (O : Finset (Site d)) (t : ℕ) (E : Set (O → A.Sym)) :
    |(A.law ε μ t (A.cyl O E)).toReal -
        (A.law ε (Measure.dirac A.zeroConfig) t (A.cyl O E)).toReal| ≤
      A.deltaO ε O t := by
  set P : A.Config → ℝ := fun x => (A.law ε (Measure.dirac x) t (A.cyl O E)).toReal with hP
  have hPm : Measurable P :=
    ENNReal.measurable_toReal.comp
      (A.measurable_law_dirac_apply h0 h1 t (A.measurableSet_cyl O E))
  have hPle : ∀ x, ‖P x‖ ≤ 1 := by
    intro x
    have := A.isProbabilityMeasure_law h0 h1 (Measure.dirac x) t
    rw [Real.norm_eq_abs, abs_le]
    simp only [hP, ← measureReal_def]
    have hnn : 0 ≤ (A.law ε (Measure.dirac x) t).real (A.cyl O E) := measureReal_nonneg
    exact ⟨by linarith, measureReal_le_one⟩
  have hint : Integrable P μ :=
    Integrable.mono' (integrable_const 1) hPm.aestronglyMeasurable (Eventually.of_forall hPle)
  rw [A.law_toReal_eq_integral h0 h1 μ t (A.measurableSet_cyl O E)]
  have hc : (A.law ε (Measure.dirac A.zeroConfig) t (A.cyl O E)).toReal =
      ∫ _, P A.zeroConfig ∂μ := by
    rw [integral_const, probReal_univ, one_smul]
  rw [hc, ← integral_sub hint (integrable_const _)]
  have := norm_integral_le_of_norm_le_const (μ := μ) (f := fun x => P x - P A.zeroConfig)
    (C := A.deltaO ε O t) (Eventually.of_forall (fun x => by
      rw [Real.norm_eq_abs]
      exact (A.abs_le_dtv O _ _ E).trans (A.dtv_le_deltaO h0 h1 O t x)))
  rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this

/-- `dtv(μΦ^t|_O, νΦ^t|_O) ≤ 2 δ_O(t)`. -/
theorem dtv_law_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ ν : Measure A.Config)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (O : Finset (Site d)) (t : ℕ) :
    A.dtv O (A.law ε μ t) (A.law ε ν t) ≤ 2 * A.deltaO ε O t := by
  refine A.dtv_le_of (fun E => ?_)
  have a := A.abs_law_sub_zero_le h0 h1 μ O t E
  have b := A.abs_law_sub_zero_le h0 h1 ν O t E
  rw [abs_sub_comm] at b
  have := abs_sub_le (A.law ε μ t (A.cyl O E)).toReal
    (A.law ε (Measure.dirac A.zeroConfig) t (A.cyl O E)).toReal
    (A.law ε ν t (A.cyl O E)).toReal
  linarith

/-- A stationary law is fixed by every `Φ^t`. -/
theorem law_of_stationary {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (π : Measure A.Config)
    [IsProbabilityMeasure π] (hπ : A.IsStationary ε π) (t : ℕ) : A.law ε π t = π := by
  induction t with
  | zero => exact A.law_zero h0 h1 π
  | succ t ih =>
    rw [A.law_succ h0 h1 t π, ih]
    exact hπ

/-- **Forgetting implies ergodicity.** If the process forgets, it is ergodic, and every stationary
law `π` satisfies `dtv(μΦ^t|_O, π|_O) ≤ 2 δ_O(t)` for every probability measure `μ`, every window
`O` and every `t ≥ 0`. -/
theorem ergodic_of_forgets {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hf : A.Forgets ε) :
    A.IsErgodic ε ∧
      ∀ π : Measure A.Config, IsProbabilityMeasure π → A.IsStationary ε π →
        ∀ μ : Measure A.Config, IsProbabilityMeasure μ → ∀ (O : Finset (Site d)) (t : ℕ),
          A.dtv O (A.law ε μ t) π ≤ 2 * A.deltaO ε O t := by
  have hbound : ∀ π : Measure A.Config, IsProbabilityMeasure π → A.IsStationary ε π →
      ∀ μ : Measure A.Config, IsProbabilityMeasure μ → ∀ (O : Finset (Site d)) (t : ℕ),
        A.dtv O (A.law ε μ t) π ≤ 2 * A.deltaO ε O t := by
    intro π _ hπ μ _ O t
    have := A.dtv_law_le h0 h1 μ π O t
    rwa [A.law_of_stationary h0 h1 π hπ t] at this
  refine ⟨?_, hbound⟩
  obtain ⟨π, hπp, hπ⟩ := A.exists_stationary h0 h1
  have hconv : ∀ μ : Measure A.Config, IsProbabilityMeasure μ →
      FNE.WeakTendsto (fun t => A.law ε μ t) π := by
    intro μ hμ
    have : ∀ t, IsProbabilityMeasure (A.law ε μ t) := fun t =>
      A.isProbabilityMeasure_law h0 h1 μ t
    rw [A.weakTendsto_iff_dtv]
    intro O
    have h2 : Tendsto (fun t => 2 * A.deltaO ε O t) atTop (𝓝 0) := by
      simpa using (hf O).const_mul 2
    exact squeeze_zero (fun t => A.dtv_nonneg _ _ _) (fun t => hbound π hπp hπ μ hμ O t) h2
  refine ⟨π, hπp, hπ, fun π' hπ'p hπ' => ?_, hconv⟩
  have hw := hconv π' hπ'p
  have hconst : (fun t => A.law ε π' t) = fun _ => π' :=
    funext (A.law_of_stationary h0 h1 π' hπ')
  rw [hconst] at hw
  exact ext_of_forall_integral_eq_of_IsFiniteMeasure
    (fun f => tendsto_nhds_unique tendsto_const_nhds (hw f))

/-! ## Memory gives two stationary laws -/

/-- **Memory gives two stationary laws** (the forgetting core's `two_invariant_of_memory`, for two
initial laws): the limits of the Cesàro averages from the two initial laws, along a common
subsequence, are stationary and differ on the cylinder that witnesses the memory. If both initial
laws are translation invariant, so are both limits. -/
theorem two_stationary_of_memory {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {μ μ' : Measure A.Config}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure μ'] (h : A.HasMemoryFrom ε μ μ') :
    ∃ π π' : Measure A.Config, π ≠ π' ∧ IsProbabilityMeasure π ∧ A.IsStationary ε π ∧
      IsProbabilityMeasure π' ∧ A.IsStationary ε π' ∧
      (A.IsTranslationInvariant μ → A.IsTranslationInvariant π) ∧
      (A.IsTranslationInvariant μ' → A.IsTranslationInvariant π') := by
  obtain ⟨O, E, α, hα, hmem⟩ := h
  obtain ⟨φ₁, hφ₁, π, hπp, hπ⟩ := A.exists_cesaro_limit h0 h1 μ (n := id) tendsto_id
  obtain ⟨φ₂, hφ₂, π', hπ'p, hπ'⟩ := A.exists_cesaro_limit h0 h1 μ' (n := φ₁)
    hφ₁.tendsto_atTop
  have hπ2 : FNE.WeakTendsto (fun m => A.cesaro ε μ (φ₁ (φ₂ m))) π :=
    fun f => (hπ f).comp hφ₂.tendsto_atTop
  have hN : Tendsto (fun m => φ₁ (φ₂ m)) atTop atTop :=
    hφ₁.tendsto_atTop.comp hφ₂.tendsto_atTop
  refine ⟨π, π', fun heq => ?_, hπp, A.isStationary_of_cesaro_limit h0 h1 _ hN π hπ2, hπ'p,
    A.isStationary_of_cesaro_limit h0 h1 _ hN π' hπ',
    fun hμ => (A.isTI_of_cesaro_limit h0 h1 hμ hN π hπ2).2,
    fun hμ' => (A.isTI_of_cesaro_limit h0 h1 hμ' hN π' hπ').2⟩
  have hgap : ∀ N : ℕ, 1 ≤ N → α ≤ ∫ y, A.cylIndicator O E y ∂(A.cesaro ε μ N) -
      ∫ y, A.cylIndicator O E y ∂(A.cesaro ε μ' N) := by
    intro N hN1
    rw [A.integral_cesaro h0 h1, A.integral_cesaro h0 h1]
    simp only [integral_cylIndicator]
    rw [← mul_sub, ← Finset.sum_sub_distrib]
    have hsum : (N : ℝ) * α ≤ ∑ t ∈ Finset.range N,
        ((A.law ε μ t (A.cyl O E)).toReal - (A.law ε μ' t (A.cyl O E)).toReal) := by
      calc (N : ℝ) * α = ∑ _t ∈ Finset.range N, α := by simp
        _ ≤ _ := Finset.sum_le_sum (fun t _ => by linarith [hmem t])
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN1
    rw [le_inv_mul_iff₀ hNpos]
    linarith
  have hlim := (hπ2 (A.cylIndicator O E)).sub (hπ' (A.cylIndicator O E))
  have hge : α ≤ ∫ y, A.cylIndicator O E y ∂π - ∫ y, A.cylIndicator O E y ∂π' := by
    refine ge_of_tendsto hlim ?_
    filter_upwards [hN.eventually_ge_atTop 1] with m hm
    exact hgap _ hm
  rw [heq, sub_self] at hge
  linarith

/-- **Theorem 7.3, last paragraph.** Memory between two translation-invariant initial laws gives
at least two translation-invariant stationary laws. -/
theorem hasTwoTIStationaryLaws_of_memory {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    {μ μ' : Measure A.Config} [IsProbabilityMeasure μ] [IsProbabilityMeasure μ']
    (hμ : A.IsTranslationInvariant μ) (hμ' : A.IsTranslationInvariant μ')
    (h : A.HasMemoryFrom ε μ μ') : A.HasTwoTIStationaryLaws ε := by
  obtain ⟨π, π', hne, hπp, hπ, hπ'p, hπ', hti, hti'⟩ := A.two_stationary_of_memory h0 h1 h
  exact ⟨π, π', hne, hπp, hπ, hti hμ, hπ'p, hπ', hti' hμ'⟩

/-- Two distinct stationary laws exclude ergodicity. -/
theorem not_ergodic_of_two {ε : ℝ} (h : A.HasTwoTIStationaryLaws ε) : ¬ A.IsErgodic ε := by
  rintro ⟨π, -, -, huniq, -⟩
  obtain ⟨μ₁, μ₂, hne, h1p, h1s, -, h2p, h2s, -⟩ := h
  exact hne ((huniq μ₁ h1p h1s).trans (huniq μ₂ h2p h2s).symm)

/-- The clauses of Theorem 9.3 at one rate from the two branches: if nonhalting gives two
translation-invariant stationary laws and halting gives forgetting together with the pullback
clause, then the rate satisfies all three clauses of `NoiseDiagram`. -/
theorem noiseDiagram_clauses {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {P : Prop}
    (hnon : ¬ P → A.HasTwoTIStationaryLaws ε)
    (hhalt : P → A.Forgets ε ∧ A.PullbackEventuallySingleton ε) :
    (A.IsErgodic ε ↔ P) ∧ (¬ P → A.HasTwoTIStationaryLaws ε) ∧
      (P → A.IsErgodic ε ∧ A.PullbackEventuallySingleton ε) := by
  have herg : P → A.IsErgodic ε := fun hP => (A.ergodic_of_forgets h0 h1 (hhalt hP).1).1
  refine ⟨⟨fun he => ?_, herg⟩, hnon, fun hP => ⟨herg hP, (hhalt hP).2⟩⟩
  by_contra hP
  exact A.not_ergodic_of_two (hnon hP) he

end UND.CA

end
