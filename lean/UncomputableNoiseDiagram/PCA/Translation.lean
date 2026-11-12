/-
# The PCA layer, part 5: translation invariance

Node P5 of `BLUEPRINT.md` (Part A.1), NEW (the forgetting core has no statement-level translation
invariance). Theorem 7.3: "The initial law and dynamics are spatially invariant, so each limit is
invariant under all six spatial coordinates."

* the global map commutes with translations (`apply_shift`); translating the start and the noise
  translates the trajectory (`run_shift`); the noise law is translation invariant
  (`noiseLaw_map_shiftNoise`);
* `(μ F_ε^t) ∘ T_a⁻¹ = (μ ∘ T_a⁻¹) F_ε^t` (`law_map_shift`), so a translation-invariant initial law
  has translation-invariant laws at all times (`isTI_law`) and translation-invariant Cesàro
  averages (`isTI_cesaro`);
* weak limits of translation-invariant probability measures are translation invariant
  (`isTI_of_weakTendsto`), hence every Cesàro limit from a translation-invariant start is a
  translation-invariant stationary law (`isTI_of_cesaro_limit`).
-/
import UncomputableNoiseDiagram.PCA.Feller

set_option autoImplicit false

noncomputable section

namespace UND.CA

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

variable {d : ℕ} (A : CA d)

/-! ## Translations of configurations and of the noise -/

theorem measurable_shift (a : Site d) : Measurable (A.shift a) :=
  Measurable.of_eval (fun w => measurable_pi_apply (w + a))

theorem continuous_shift (a : Site d) : Continuous (A.shift a) :=
  continuous_pi (fun w => continuous_apply (w + a))

/-- The global map commutes with every translation. -/
theorem apply_shift (a : Site d) (x : A.Config) :
    A.apply (A.shift a x) = A.shift a (A.apply x) := by
  funext w
  simp only [apply, shift]
  congr 1
  funext z
  rw [add_right_comm]

/-- The spatial translate of a noise realisation. -/
def shiftNoise (a : Site d) (ω : A.Noise) : A.Noise := fun p => ω (p.1, p.2 + a)

theorem measurable_shiftNoise (a : Site d) : Measurable (A.shiftNoise a) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

/-- Translating the start and the noise translates the trajectory. -/
theorem run_shift (a : Site d) (x : A.Config) (ω : A.Noise) (t : ℕ) :
    A.run (A.shift a x) (A.shiftNoise a ω) t = A.shift a (A.run x ω t) := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ, run_succ, ih]
    funext w
    simp only [update, shiftNoise, shift, apply_shift]

/-- The noise law is invariant under spatial translations. -/
theorem noiseLaw_map_shiftNoise {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (a : Site d) :
    (A.noiseLaw ε).map (A.shiftNoise a) = A.noiseLaw ε := by
  have := A.isProbabilityMeasure_noiseSite h0 h1
  have hinj : Function.Injective (fun p : ℕ × Site d => (p.1, p.2 + a)) := by
    rintro ⟨t, v⟩ ⟨t', v'⟩ h
    simp only [Prod.mk.injEq, add_left_inj] at h
    rw [h.1, h.2]
  exact Measure.map_infinitePi_infinitePi_of_inj hinj

/-! ## Laws of translates -/

/-- `(μ F_ε^t) ∘ T_a⁻¹ = (μ ∘ T_a⁻¹) F_ε^t`. -/
theorem law_map_shift {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure A.Config)
    [IsProbabilityMeasure μ] (a : Site d) (t : ℕ) :
    (A.law ε μ t).map (A.shift a) = A.law ε (μ.map (A.shift a)) t := by
  have := A.isProbabilityMeasure_noiseLaw h0 h1
  have hrun := A.measurable_run t
  have hsh := A.measurable_shift a
  have hPM := Measure.map_prod_map μ (A.noiseLaw ε) hsh (A.measurable_shiftNoise a)
  rw [A.noiseLaw_map_shiftNoise h0 h1] at hPM
  unfold law
  rw [hPM, Measure.map_map hsh hrun, Measure.map_map hrun (hsh.prodMap (A.measurable_shiftNoise a))]
  congr 1
  funext p
  exact (A.run_shift a p.1 p.2 t).symm

/-- A translation-invariant initial law has translation-invariant laws at all times. -/
theorem isTI_law {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {μ : Measure A.Config}
    [IsProbabilityMeasure μ] (hμ : A.IsTranslationInvariant μ) (t : ℕ) :
    A.IsTranslationInvariant (A.law ε μ t) := fun a => by
  rw [A.law_map_shift h0 h1 μ a t, hμ a]

/-- A translation-invariant initial law has translation-invariant Cesàro averages. -/
theorem isTI_cesaro {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {μ : Measure A.Config}
    [IsProbabilityMeasure μ] (hμ : A.IsTranslationInvariant μ) (n : ℕ) :
    A.IsTranslationInvariant (A.cesaro ε μ n) := fun a => by
  ext s hs
  have hsh := A.measurable_shift a
  rw [Measure.map_apply hsh hs]
  simp only [cesaro, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, smul_eq_mul]
  congr 1
  refine Finset.sum_congr rfl (fun t _ => ?_)
  rw [← Measure.map_apply hsh hs, A.isTI_law h0 h1 hμ t a]

/-- Weak limits of translation-invariant measures are translation invariant (`T_a` is
continuous). -/
theorem isTI_of_weakTendsto (μs : ℕ → Measure A.Config) (π : Measure A.Config)
    [IsProbabilityMeasure π] (hμ : ∀ m, A.IsTranslationInvariant (μs m))
    (h : FNE.WeakTendsto μs π) : A.IsTranslationInvariant π := by
  intro a
  have hsh := A.measurable_shift a
  have : IsProbabilityMeasure (π.map (A.shift a)) := (Measure.isProbabilityMeasure_map_iff hsh.aemeasurable).2 inferInstance
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
  let g : A.Config →ᵇ ℝ := f.compContinuous ⟨A.shift a, A.continuous_shift a⟩
  have hg : ∀ ν : Measure A.Config, ∫ x, f x ∂(ν.map (A.shift a)) = ∫ x, g x ∂ν := fun ν =>
    integral_map hsh.aemeasurable f.continuous.aestronglyMeasurable
  rw [hg]
  have e : ∀ m, ∫ x, g x ∂(μs m) = ∫ x, f x ∂(μs m) := by
    intro m
    rw [← hg, hμ m a]
  have h1 := h g
  simp only [e] at h1
  exact tendsto_nhds_unique h1 (h f)

/-- Every Cesàro limit from a translation-invariant start is a translation-invariant stationary
law (Theorem 7.3). -/
theorem isTI_of_cesaro_limit {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {μ : Measure A.Config}
    [IsProbabilityMeasure μ] (hμ : A.IsTranslationInvariant μ) {n : ℕ → ℕ}
    (hn : Tendsto n atTop atTop) (π : Measure A.Config) [IsProbabilityMeasure π]
    (hπ : FNE.WeakTendsto (fun m => A.cesaro ε μ (n m)) π) :
    A.IsStationary ε π ∧ A.IsTranslationInvariant π :=
  ⟨A.isStationary_of_cesaro_limit h0 h1 μ hn π hπ,
    A.isTI_of_weakTendsto _ π (fun m => A.isTI_cesaro h0 h1 hμ (n m)) hπ⟩

end UND.CA

end
