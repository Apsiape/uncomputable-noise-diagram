/-
# The PCA layer, part 4: the Feller property, Cesàro limits, weak convergence on cylinders

Node P4 of `BLUEPRINT.md` (Part A.1). Ported from the forgetting core
(`FixedNoiseErgodicity/Section2/Feller.lean`, same authors, v4.35 version) to an arbitrary
cellular automaton `A : CA d` (decision D3). Proofs follow the originals line by line; the default
symbol of `continuous_of_local` and `extOf` is `0 : Fin |Σ|` instead of `⊥`.

* continuity of the global map and of the process in the start (product topology);
* `Phi`: `Φf(x) = E_x f(X_1)`; `integral_law`: `∫ f d(μΦ^t) = ∫ (∫ f d(δ_xΦ^t)) dμ(x)`;
* the Feller property `continuous_Phi` (Theorem 7.3: "the kernel is Feller, since updates are
  local"); the Cesàro averages `μ̄_n = (1/n) Σ_{t<n} μΦ^t` have a weak limit along a subsequence of
  every `n_m → ∞` (`exists_cesaro_limit`), and every such limit is stationary
  (`isStationary_of_cesaro_limit`: "the difference of an average and its one-step image is the
  initial law minus the final law, divided by the averaging length"); a stationary law exists
  (`exists_stationary`, Lemma 8.5: "existence of a stationary law follows from Feller
  compactness");
* for probability measures, `μ_t → π` weakly iff `μ_t(cyl O ℰ) → π(cyl O ℰ)` for every window `O`
  and `ℰ ⊆ Σ^O` (`weakTendsto_iff_cyl`), iff `dtv(μ_t|_O, π|_O) → 0` for every window
  (`weakTendsto_iff_dtv`).
-/
import UncomputableNoiseDiagram.PCA.Cylinder
import Mathlib.MeasureTheory.Measure.Prokhorov
import Mathlib.MeasureTheory.Measure.LevyProkhorovMetric
import Mathlib.MeasureTheory.Measure.HasOuterApproxClosed
import Mathlib.MeasureTheory.Integral.Bochner.SumMeasure
import Mathlib.Topology.Sequences
import Mathlib.Analysis.SpecificLimits.Basic

set_option autoImplicit false

noncomputable section

namespace UND.CA

open MeasureTheory Filter Topology
open scoped ENNReal BoundedContinuousFunction

variable {d : ℕ} (A : CA d)

/-! ## Continuity of the rule and of the process -/

/-- A function of configurations that only reads a finite window is continuous. -/
theorem continuous_of_local {β : Type*} [TopologicalSpace β] (W : Finset (Site d))
    (f : A.Config → β) (hf : ∀ y y' : A.Config, (∀ w ∈ W, y w = y' w) → f y = f y') :
    Continuous f := by
  classical
  let ext : (W → A.Sym) → A.Config := fun z w => if h : w ∈ W then z ⟨w, h⟩ else
    ⟨0, A.numSymbols_pos⟩
  let r : A.Config → (W → A.Sym) := fun y w => y w.1
  have hr : Continuous r := continuous_pi (fun w => continuous_apply w.1)
  have heq : f = (fun z => f (ext z)) ∘ r := by
    funext y
    exact hf _ _ (fun w hw => by simp [ext, r, hw])
  rw [heq]
  exact continuous_of_discreteTopology.comp hr

theorem continuous_apply_apply (w : Site d) : Continuous (fun x : A.Config => A.apply x w) :=
  A.continuous_of_local (A.window w) _ fun _ _ h => A.apply_congr fun z hz =>
    h _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)

/-- The global map `F` is continuous (Section 2: updates are local). -/
theorem continuous_applyMap : Continuous A.apply :=
  continuous_pi A.continuous_apply_apply

/-- For a fixed noise, `X_t` is a continuous function of the start. -/
theorem continuous_run (ω : A.Noise) (t : ℕ) : Continuous (fun x : A.Config => A.run x ω t) := by
  induction t with
  | zero => exact continuous_id
  | succ t ih =>
    refine continuous_pi (fun v => ?_)
    by_cases h : (ω (t, v)).1 = true
    · have : (fun x : A.Config => A.run x ω (t + 1) v) = fun _ => (ω (t, v)).2 := by
        funext x
        simp [run_succ, update, h]
      rw [this]
      exact continuous_const
    · have : (fun x : A.Config => A.run x ω (t + 1) v) =
          fun x => A.apply (A.run x ω t) v := by
        funext x
        simp [run_succ, update, h]
      rw [this]
      exact (A.continuous_apply_apply v).comp ih

/-! ## The operator `Φ` and the integral form of the mixture formula -/

/-- `Φf(x) = E_x f(X_1)`. -/
def Phi (ε : ℝ) (f : A.Config → ℝ) (x : A.Config) : ℝ :=
  ∫ y, f y ∂(A.law ε (Measure.dirac x) 1)

theorem integral_law_dirac {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (f : A.Config →ᵇ ℝ)
    (x : A.Config) (t : ℕ) :
    ∫ y, f y ∂(A.law ε (Measure.dirac x) t) = ∫ ω, f (A.run x ω t) ∂(A.noiseLaw ε) := by
  have hm : Measurable (fun ω : A.Noise => A.run x ω t) :=
    (A.measurable_run t).comp measurable_prodMk_left
  rw [A.law_dirac h0 h1, integral_map hm.aemeasurable f.continuous.aestronglyMeasurable]

/-- `∫ f d(μΦ^t) = ∫ (∫ f d(δ_x Φ^t)) dμ(x)` for bounded continuous `f`. -/
theorem integral_law {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure A.Config)
    [IsProbabilityMeasure μ] (t : ℕ) (f : A.Config →ᵇ ℝ) :
    ∫ y, f y ∂(A.law ε μ t) = ∫ x, (∫ y, f y ∂(A.law ε (Measure.dirac x) t)) ∂μ := by
  have := A.isProbabilityMeasure_noiseLaw h0 h1
  have hm := A.measurable_run t
  rw [show A.law ε μ t = (μ.prod (A.noiseLaw ε)).map (fun p => A.run p.1 p.2 t) from rfl,
    integral_map hm.aemeasurable f.continuous.aestronglyMeasurable, integral_prod]
  · congr 1
    funext x
    rw [A.integral_law_dirac h0 h1]
  · refine Integrable.mono' (integrable_const ‖f‖)
      (f.continuous.measurable.comp hm).aestronglyMeasurable
      (Eventually.of_forall (fun p => f.norm_coe_le_norm _))

/-- **The Feller property** (Theorem 7.3): `Φf` is continuous for every continuous `f`. -/
theorem continuous_Phi {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (f : A.Config → ℝ)
    (hf : Continuous f) : Continuous (A.Phi ε f) := by
  have := A.isProbabilityMeasure_noiseLaw h0 h1
  let g : A.Config →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact ⟨f, hf⟩
  have hPhi : A.Phi ε f = fun x => ∫ ω, g (A.run x ω 1) ∂(A.noiseLaw ε) := by
    funext x
    exact A.integral_law_dirac h0 h1 g x 1
  rw [hPhi]
  refine continuous_of_dominated (bound := fun _ => ‖g‖) (fun x => ?_)
    (fun x => Eventually.of_forall (fun ω => g.norm_coe_le_norm _)) (integrable_const _)
    (Eventually.of_forall (fun ω => g.continuous.comp (A.continuous_run ω 1)))
  exact (g.continuous.measurable.comp
    ((A.measurable_run 1).comp measurable_prodMk_left)).aestronglyMeasurable

/-- `Φf` as a bounded continuous function. -/
def PhiBCF {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (f : A.Config →ᵇ ℝ) : A.Config →ᵇ ℝ :=
  BoundedContinuousFunction.mkOfCompact ⟨A.Phi ε f, A.continuous_Phi h0 h1 f f.continuous⟩

/-- `(μΦ^t)(Φf) = (μΦ^{t+1})(f)`. -/
theorem integral_Phi_law {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure A.Config)
    [IsProbabilityMeasure μ] (t : ℕ) (f : A.Config →ᵇ ℝ) :
    ∫ x, A.Phi ε f x ∂(A.law ε μ t) = ∫ y, f y ∂(A.law ε μ (t + 1)) := by
  have := A.isProbabilityMeasure_law h0 h1 μ t
  rw [A.law_succ h0 h1 t μ, A.integral_law h0 h1 (A.law ε μ t) 1 f]
  rfl

/-! ## Cesàro averages and stationary laws -/

/-- Theorem 7.3: the temporal Cesàro averages `μ̄_n = (1/n) Σ_{t=0}^{n-1} μΦ^t`. -/
def cesaro (ε : ℝ) (μ : Measure A.Config) (n : ℕ) : Measure A.Config :=
  (n : ℝ≥0∞)⁻¹ • ∑ t ∈ Finset.range n, A.law ε μ t

theorem isProbabilityMeasure_cesaro {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure A.Config)
    [IsProbabilityMeasure μ] {n : ℕ} (hn : 1 ≤ n) : IsProbabilityMeasure (A.cesaro ε μ n) := by
  constructor
  have : ∀ t, A.law ε μ t Set.univ = 1 := fun t =>
    (A.isProbabilityMeasure_law h0 h1 μ t).measure_univ
  simp only [cesaro, Measure.smul_apply, Measure.coe_finsetSum, Finset.sum_apply, this,
    Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (by exact_mod_cast (show n ≠ 0 by omega)) (by simp)

theorem integral_cesaro {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure A.Config)
    [IsProbabilityMeasure μ] (n : ℕ) (f : A.Config →ᵇ ℝ) :
    ∫ y, f y ∂(A.cesaro ε μ n) = (n : ℝ)⁻¹ * ∑ t ∈ Finset.range n, ∫ y, f y ∂(A.law ε μ t) := by
  unfold cesaro
  rw [integral_smul_measure, integral_finsetSum_measure]
  · simp [ENNReal.toReal_inv]
  · intro t _
    have := A.isProbabilityMeasure_law h0 h1 μ t
    exact f.integrable _

/-- **Theorem 7.3**, the Cesàro step: every weak limit of the averages along `n_m → ∞` is
stationary. -/
theorem isStationary_of_cesaro_limit {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure A.Config)
    [IsProbabilityMeasure μ] {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) (π : Measure A.Config)
    [IsProbabilityMeasure π] (hπ : FNE.WeakTendsto (fun m => A.cesaro ε μ (n m)) π) :
    A.IsStationary ε π := by
  have := A.isProbabilityMeasure_law h0 h1 π 1
  refine ext_of_forall_integral_eq_of_IsFiniteMeasure (fun f => ?_)
  set g := A.PhiBCF h0 h1 f with hg
  have hgx : ∀ x, g x = A.Phi ε f x := fun _ => rfl
  have hlhs : ∫ y, f y ∂(A.law ε π 1) = ∫ x, g x ∂π := by
    rw [A.integral_law h0 h1 π 1 f]
    rfl
  rw [hlhs]
  have hdiff : Tendsto (fun m => ∫ x, g x ∂(A.cesaro ε μ (n m)) -
      ∫ x, f x ∂(A.cesaro ε μ (n m))) atTop (𝓝 0) := by
    have hbound : ∀ N : ℕ, 1 ≤ N → |∫ x, g x ∂(A.cesaro ε μ N) -
        ∫ x, f x ∂(A.cesaro ε μ N)| ≤ 2 * ‖f‖ / N := by
      intro N hN
      rw [A.integral_cesaro h0 h1, A.integral_cesaro h0 h1]
      have htel : ∑ t ∈ Finset.range N, ∫ x, g x ∂(A.law ε μ t) -
          ∑ t ∈ Finset.range N, ∫ x, f x ∂(A.law ε μ t) =
          ∫ x, f x ∂(A.law ε μ N) - ∫ x, f x ∂(A.law ε μ 0) := by
        rw [← Finset.sum_sub_distrib]
        simp only [hgx, A.integral_Phi_law h0 h1]
        exact Finset.sum_range_sub (fun t => ∫ x, f x ∂(A.law ε μ t)) N
      rw [← mul_sub, htel, abs_mul, abs_inv, Nat.abs_cast, ← div_eq_inv_mul]
      gcongr
      have := A.isProbabilityMeasure_law h0 h1 μ N
      have := A.isProbabilityMeasure_law h0 h1 μ 0
      have b1 := f.norm_integral_le_norm (A.law ε μ N)
      have b2 := f.norm_integral_le_norm (A.law ε μ 0)
      rw [Real.norm_eq_abs] at b1 b2
      calc |∫ x, f x ∂(A.law ε μ N) - ∫ x, f x ∂(A.law ε μ 0)|
          ≤ |∫ x, f x ∂(A.law ε μ N)| + |∫ x, f x ∂(A.law ε μ 0)| := abs_sub _ _
        _ ≤ 2 * ‖f‖ := by linarith
    have hlim : Tendsto (fun m => 2 * ‖f‖ / (n m : ℝ)) atTop (𝓝 0) :=
      (tendsto_const_div_atTop_nhds_zero_nat (2 * ‖f‖)).comp hn
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [hn.eventually_ge_atTop 1] with m hm
    rw [Real.norm_eq_abs]
    exact hbound (n m) hm
  have hlim := (hπ g).sub (hπ f)
  have := tendsto_nhds_unique hlim hdiff
  linarith

/-- Feller compactness: for every `μ` and every `n_m → ∞`, the averages have a weak limit along a
subsequence; the limit is a probability measure. -/
theorem exists_cesaro_limit {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure A.Config)
    [IsProbabilityMeasure μ] {n : ℕ → ℕ} (hn : Tendsto n atTop atTop) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∃ π : Measure A.Config, IsProbabilityMeasure π ∧
      FNE.WeakTendsto (fun m => A.cesaro ε μ (n (φ m))) π := by
  classical
  let ν : ℕ → ProbabilityMeasure A.Config := fun m =>
    if h : 1 ≤ n m then ⟨A.cesaro ε μ (n m), A.isProbabilityMeasure_cesaro h0 h1 μ h⟩
    else ⟨μ, inferInstance⟩
  obtain ⟨π, -, φ, hφ, hlim⟩ := isCompact_univ.tendsto_subseq (x := ν) (fun _ => Set.mem_univ _)
  refine ⟨φ, hφ, π, inferInstance, fun f => ?_⟩
  have h := (ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.mp hlim) f
  refine h.congr' ?_
  filter_upwards [(hn.comp hφ.tendsto_atTop).eventually_ge_atTop 1] with m hm
  simp only [Function.comp_apply] at hm
  have hν : ν (φ m) = (⟨A.cesaro ε μ (n (φ m)),
      A.isProbabilityMeasure_cesaro h0 h1 μ hm⟩ : ProbabilityMeasure A.Config) :=
    dite_eq_left hm
  simp only [Function.comp_apply, hν, ProbabilityMeasure.coe_mk]

/-- Lemma 8.5 / Theorem 7.3: a stationary probability law exists (Feller compactness). -/
theorem exists_stationary {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    ∃ π : Measure A.Config, IsProbabilityMeasure π ∧ A.IsStationary ε π := by
  obtain ⟨φ, hφ, π, hπ, hlim⟩ := A.exists_cesaro_limit h0 h1
    (Measure.dirac A.zeroConfig) (n := id) tendsto_id
  exact ⟨π, hπ, A.isStationary_of_cesaro_limit h0 h1 _ (tendsto_id.comp hφ.tendsto_atTop) π hlim⟩

/-! ## Weak convergence is convergence on cylinders -/

/-- The configuration equal to `z` on the window `W` and to `0` elsewhere. -/
def extOf (W : Finset (Site d)) (z : W → A.Sym) : A.Config :=
  fun w => if h : w ∈ W then z ⟨w, h⟩ else ⟨0, A.numSymbols_pos⟩

/-- Compactness of `Σ^{ℤ^d}`: a continuous `f` varies by less than `δ` between configurations that
agree on some finite window. -/
theorem exists_window_approx (f : A.Config → ℝ) (hf : Continuous f) {δ : ℝ} (hδ : 0 < δ) :
    ∃ W : Finset (Site d), ∀ y y' : A.Config, (∀ w ∈ W, y w = y' w) → |f y - f y'| < δ := by
  classical
  have hloc : ∀ x : A.Config, ∃ W : Finset (Site d),
      ∀ y : A.Config, (∀ w ∈ W, y w = x w) → |f y - f x| < δ / 2 := by
    intro x
    have hU : IsOpen {y : A.Config | |f y - f x| < δ / 2} :=
      isOpen_lt (continuous_abs.comp (hf.sub continuous_const)) continuous_const
    obtain ⟨I, u, hu, hsub⟩ := isOpen_pi_iff.mp hU x (by simp; linarith)
    refine ⟨I, fun y hy => hsub ?_⟩
    intro a ha
    rw [hy a ha]
    exact (hu a ha).2
  choose W hW using hloc
  let U : A.Config → Set A.Config := fun x => {y | ∀ w ∈ W x, y w = x w}
  have hUn : ∀ x, U x ∈ 𝓝 x := by
    intro x
    refine IsOpen.mem_nhds ?_ (fun w _ => rfl)
    have : U x = ⋂ w ∈ W x, (fun y : A.Config => y w) ⁻¹' {x w} := by
      ext y
      simp [U]
    rw [this]
    exact isOpen_biInter_finset (fun w _ => (isOpen_discrete _).preimage (continuous_apply w))
  obtain ⟨T, hT⟩ := CompactSpace.elim_nhds_subcover U hUn
  refine ⟨T.biUnion W, fun y y' hyy' => ?_⟩
  have hy : y ∈ ⋃ x ∈ T, U x := by
    rw [hT]
    trivial
  obtain ⟨x, hxT, hyx⟩ := Set.mem_iUnion₂.mp hy
  have hy'x : ∀ w ∈ W x, y' w = x w := fun w hw =>
    (hyy' w (Finset.mem_biUnion.mpr ⟨x, hxT, hw⟩)).symm.trans (hyx w hw)
  have h1 := hW x y hyx
  have h2 := hW x y' hy'x
  calc |f y - f y'| = |(f y - f x) - (f y' - f x)| := by ring_nf
    _ ≤ |f y - f x| + |f y' - f x| := abs_sub _ _
    _ < δ / 2 + δ / 2 := add_lt_add h1 h2
    _ = δ := by ring

/-- The integral of a function of the window `W` is a finite sum over cylinders. -/
theorem integral_window (W : Finset (Site d)) (F : (W → A.Sym) → ℝ) (ν : Measure A.Config)
    [IsFiniteMeasure ν] :
    ∫ y, F (fun w : W => y w.1) ∂ν = ∑ z : W → A.Sym, (ν (A.cyl W {z})).toReal * F z := by
  classical
  have hr : Measurable (fun y : A.Config => fun w : W => y w.1) :=
    Measurable.of_eval (fun w => measurable_pi_apply w.1)
  rw [← integral_map hr.aemeasurable (measurable_of_countable F).aestronglyMeasurable,
    integral_fintype Integrable.of_finite]
  refine Finset.sum_congr rfl (fun z _ => ?_)
  rw [smul_eq_mul, measureReal_def, Measure.map_apply hr (measurableSet_singleton z)]
  rfl

/-- Convergence on every cylinder implies weak convergence (probability measures). -/
theorem weakTendsto_of_cyl (μs : ℕ → Measure A.Config) [∀ t, IsProbabilityMeasure (μs t)]
    (π : Measure A.Config) [IsProbabilityMeasure π]
    (h : ∀ (O : Finset (Site d)) (E : Set (O → A.Sym)),
      Tendsto (fun t => (μs t (A.cyl O E)).toReal) atTop (𝓝 (π (A.cyl O E)).toReal)) :
    FNE.WeakTendsto μs π := by
  classical
  intro f
  rw [Metric.tendsto_atTop]
  intro δ hδ
  obtain ⟨W, hW⟩ := A.exists_window_approx f f.continuous (δ := δ / 4) (by positivity)
  let F : (W → A.Sym) → ℝ := fun z => f (A.extOf W z)
  let g : A.Config →ᵇ ℝ := BoundedContinuousFunction.mkOfCompact
    ⟨fun y => F (fun w : W => y w.1), A.continuous_of_local W _ (fun y y' hyy' => by
      simp only [F]
      congr 2
      funext w
      exact hyy' w.1 w.2)⟩
  have hgf : ∀ y, |f y - g y| < δ / 4 := by
    intro y
    refine hW y _ (fun w hw => ?_)
    simp [extOf, hw]
  have happrox : ∀ ν : Measure A.Config, IsProbabilityMeasure ν →
      |∫ y, f y ∂ν - ∫ y, g y ∂ν| ≤ δ / 4 := by
    intro ν _
    rw [← integral_sub (f.integrable ν) (g.integrable ν)]
    have := norm_integral_le_of_norm_le_const (μ := ν) (f := fun y => f y - g y) (C := δ / 4)
      (Eventually.of_forall (fun y => (hgf y).le))
    rwa [probReal_univ, mul_one, Real.norm_eq_abs] at this
  have hconv : Tendsto (fun t => ∫ y, g y ∂(μs t)) atTop (𝓝 (∫ y, g y ∂π)) := by
    have e : ∀ ν : Measure A.Config, IsFiniteMeasure ν →
        ∫ y, g y ∂ν = ∑ z : W → A.Sym, (ν (A.cyl W {z})).toReal * F z :=
      fun ν _ => A.integral_window W F ν
    simp only [e _ inferInstance]
    exact tendsto_finsetSum _ (fun z _ => (h W {z}).mul_const _)
  obtain ⟨N, hN⟩ := Metric.tendsto_atTop.mp hconv (δ / 4) (by positivity)
  refine ⟨N, fun t ht => ?_⟩
  have h2 := hN t ht
  rw [Real.dist_eq] at h2 ⊢
  have a1 := happrox (μs t) inferInstance
  have a2 := happrox π inferInstance
  calc |∫ y, f y ∂(μs t) - ∫ y, f y ∂π|
      ≤ |∫ y, f y ∂(μs t) - ∫ y, g y ∂(μs t)| + |∫ y, g y ∂(μs t) - ∫ y, g y ∂π| +
          |∫ y, g y ∂π - ∫ y, f y ∂π| := by
        have := abs_sub_le (∫ y, f y ∂(μs t)) (∫ y, g y ∂(μs t)) (∫ y, f y ∂π)
        have := abs_sub_le (∫ y, g y ∂(μs t)) (∫ y, g y ∂π) (∫ y, f y ∂π)
        linarith
    _ < δ := by
        rw [abs_sub_comm (∫ y, g y ∂π)]
        linarith

/-- For probability measures, `μ_t → π` weakly iff `μ_t(cyl O ℰ) → π(cyl O ℰ)` for every window
`O` and every `ℰ ⊆ Σ^O`. -/
theorem weakTendsto_iff_cyl (μs : ℕ → Measure A.Config) [∀ t, IsProbabilityMeasure (μs t)]
    (π : Measure A.Config) [IsProbabilityMeasure π] :
    FNE.WeakTendsto μs π ↔ ∀ (O : Finset (Site d)) (E : Set (O → A.Sym)),
      Tendsto (fun t => (μs t (A.cyl O E)).toReal) atTop (𝓝 (π (A.cyl O E)).toReal) := by
  refine ⟨fun h O E => ?_, A.weakTendsto_of_cyl μs π⟩
  have := h (A.cylIndicator O E)
  simpa only [integral_cylIndicator] using this

/-- For probability measures, `μ_t → π` weakly iff `dtv(μ_t|_O, π|_O) → 0` for every window. -/
theorem weakTendsto_iff_dtv (μs : ℕ → Measure A.Config) [∀ t, IsProbabilityMeasure (μs t)]
    (π : Measure A.Config) [IsProbabilityMeasure π] :
    FNE.WeakTendsto μs π ↔ ∀ O : Finset (Site d), Tendsto (fun t => A.dtv O (μs t) π) atTop (𝓝 0) := by
  classical
  rw [A.weakTendsto_iff_cyl]
  constructor
  · intro h O
    have hsum : Tendsto (fun t => ∑ E : Set (O → A.Sym),
        |(μs t (A.cyl O E)).toReal - (π (A.cyl O E)).toReal|) atTop (𝓝 0) := by
      have := tendsto_finsetSum (Finset.univ : Finset (Set (O → A.Sym)))
        (fun E _ => ((h O E).sub_const (π (A.cyl O E)).toReal).abs)
      simpa using this
    refine squeeze_zero (fun t => A.dtv_nonneg _ _ _) (fun t => A.dtv_le_of (fun E => ?_)) hsum
    exact Finset.single_le_sum (f := fun E : Set (O → A.Sym) =>
      |(μs t (A.cyl O E)).toReal - (π (A.cyl O E)).toReal|) (fun _ _ => abs_nonneg _)
      (Finset.mem_univ E)
  · intro h O E
    have h' : Tendsto (fun t => |(μs t (A.cyl O E)).toReal - (π (A.cyl O E)).toReal|) atTop
        (𝓝 0) :=
      squeeze_zero (fun t => abs_nonneg _) (fun t => A.abs_le_dtv O _ _ E) (h O)
    rw [tendsto_iff_norm_sub_tendsto_zero]
    simpa [Real.norm_eq_abs] using h'

end UND.CA

end
