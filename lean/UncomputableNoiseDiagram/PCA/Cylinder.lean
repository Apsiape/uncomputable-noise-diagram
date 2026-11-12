/-
# The PCA layer, part 3: cylinders, window total variation, memory, coupling

Parts of nodes P4, P6 and P7 of `BLUEPRINT.md` (Part A.1). Ported from the forgetting core
(`FixedNoiseErgodicity/Section2/Ergodic.lean`, same authors, v4.35 version) to an arbitrary
cellular automaton `A : CA d` (decision D3); the reference start `⊥` of the forgetting core is the
all-zero configuration `zeroConfig`.

* the cylinder `{y : y|_O ∈ ℰ}` of a finite window `O` and its indicator, a bounded continuous
  function (`cyl`, `cylIndicator`, `integral_cylIndicator`);
* memory between two initial laws (`HasMemoryFrom`; the forgetting core's `HasMemory` is the case
  of two point masses) and its direct consequence `not_ergodic_of_memoryFrom`;
* window total variation `dtv`, `δ_O(t)` (`deltaO`) and forgetting (`Forgets`);
* NEW (for Lemma 8.5): the coupling bound `dtv_law_dirac_le` (two starts driven by the same noise
  are within the probability that they disagree on the window) and `forgets_of_coupling`
  (if the all-start disagreement probability on every window tends to zero, the process forgets).
  The disagreement events quantify over all starts and need not be measurable; the bound uses
  the outer measure.
-/
import UncomputableNoiseDiagram.PCA.Markov
import Mathlib.MeasureTheory.Integral.Bochner.Set

set_option autoImplicit false

noncomputable section

namespace UND.CA

open MeasureTheory Filter Topology
open scoped ENNReal

variable {d : ℕ} (A : CA d)

/-- The reference configuration: the symbol `0` at every site. -/
def zeroConfig : A.Config := fun _ => ⟨0, A.numSymbols_pos⟩

instance instNonemptyConfig : Nonempty A.Config := ⟨A.zeroConfig⟩

/-! ## Cylinders -/

/-- The cylinder `{y : y|_O ∈ ℰ}` of a finite window `O`. -/
def cyl (O : Finset (Site d)) (E : Set (O → A.Sym)) : Set A.Config :=
  {y | (fun w : O => y w.1) ∈ E}

theorem continuous_restrictWindow (O : Finset (Site d)) :
    Continuous (fun y : A.Config => fun w : O => y w.1) :=
  continuous_pi (fun w => continuous_apply w.1)

theorem measurable_restrictWindow (O : Finset (Site d)) :
    Measurable (fun y : A.Config => fun w : O => y w.1) :=
  Measurable.of_eval (fun w => measurable_pi_apply w.1)

theorem measurableSet_cyl (O : Finset (Site d)) (E : Set (O → A.Sym)) :
    MeasurableSet (A.cyl O E) :=
  (A.measurable_restrictWindow O) E.to_countable.measurableSet

/-- The indicator of a cylinder, a bounded continuous function (cylinders are clopen). -/
def cylIndicator (O : Finset (Site d)) (E : Set (O → A.Sym)) :
    BoundedContinuousFunction A.Config ℝ :=
  BoundedContinuousFunction.mkOfBound
    ⟨(A.cyl O E).indicator 1, by
      have : (A.cyl O E).indicator (1 : A.Config → ℝ) =
          E.indicator 1 ∘ (fun y : A.Config => fun w : O => y w.1) := by
        funext y
        exact Set.indicator_comp_right (s := E) (g := (1 : (O → A.Sym) → ℝ))
          (fun y : A.Config => fun w : O => y w.1)
      rw [this]
      exact continuous_of_discreteTopology.comp (A.continuous_restrictWindow O)⟩
    1 (by
      intro y y'
      simp only [ContinuousMap.coe_mk, Set.indicator, Pi.one_apply]
      split_ifs <;> norm_num)

theorem integral_cylIndicator (O : Finset (Site d)) (E : Set (O → A.Sym))
    (μ : Measure A.Config) :
    ∫ y, A.cylIndicator O E y ∂μ = (μ (A.cyl O E)).toReal := by
  have h : (fun y => A.cylIndicator O E y) = (A.cyl O E).indicator 1 := rfl
  rw [h, integral_indicator_one (A.measurableSet_cyl O E), measureReal_def]

/-! ## Memory -/

/-- Memory between two initial laws `μ, μ'`: a window `O`, a set `ℰ ⊆ Σ^O` and `α > 0` with
`P_μ(X_t|_O ∈ ℰ) ≥ P_{μ'}(X_t|_O ∈ ℰ) + α` for every `t ≥ 0`. (The forgetting core's
`HasMemory` is the case `μ = δ_x`, `μ' = δ_{x'}`; Theorem 7.3 uses two translation-invariant
initial laws.) -/
def HasMemoryFrom (ε : ℝ) (μ μ' : Measure A.Config) : Prop :=
  ∃ (O : Finset (Site d)) (E : Set (O → A.Sym)) (α : ℝ), 0 < α ∧
    ∀ t, (A.law ε μ' t (A.cyl O E)).toReal + α ≤ (A.law ε μ t (A.cyl O E)).toReal

/-- Memory excludes ergodicity (the forgetting core's `not_ergodic_of_memory`, for two initial
laws): under ergodicity both laws converge weakly to `π`, and the cylinder indicator is bounded
and continuous. -/
theorem not_ergodic_of_memoryFrom {ε : ℝ} {μ μ' : Measure A.Config} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] (h : A.HasMemoryFrom ε μ μ') : ¬ A.IsErgodic ε := by
  rintro ⟨π, -, -, -, hconv⟩
  obtain ⟨O, E, α, hα, hmem⟩ := h
  have hx := hconv μ inferInstance (A.cylIndicator O E)
  have hx' := hconv μ' inferInstance (A.cylIndicator O E)
  simp only [integral_cylIndicator] at hx hx'
  have hd := hx.sub hx'
  rw [sub_self] at hd
  have : α ≤ 0 := ge_of_tendsto' hd (fun t => by linarith [hmem t])
  linarith

/-! ## Total variation on windows, `δ_O(t)`, forgetting -/

/-- `dtv(μ|_O, ν|_O) = max_{ℰ ⊆ Σ^O} |μ(cyl O ℰ) - ν(cyl O ℰ)|`. -/
def dtv (O : Finset (Site d)) (μ ν : Measure A.Config) : ℝ :=
  ⨆ E : Set (O → A.Sym), |(μ (A.cyl O E)).toReal - (ν (A.cyl O E)).toReal|

/-- `δ_O(t) = sup_x dtv(Law_x(X_t|_O), Law_0(X_t|_O))`. -/
def deltaO (ε : ℝ) (O : Finset (Site d)) (t : ℕ) : ℝ :=
  ⨆ x : A.Config,
    A.dtv O (A.law ε (Measure.dirac x) t) (A.law ε (Measure.dirac A.zeroConfig) t)

/-- The process *forgets* if `δ_O(t) → 0` as `t → ∞` for every finite window `O`. -/
def Forgets (ε : ℝ) : Prop :=
  ∀ O : Finset (Site d), Tendsto (A.deltaO ε O) atTop (𝓝 0)

theorem abs_le_dtv (O : Finset (Site d)) (μ ν : Measure A.Config) (E : Set (O → A.Sym)) :
    |(μ (A.cyl O E)).toReal - (ν (A.cyl O E)).toReal| ≤ A.dtv O μ ν :=
  le_ciSup (f := fun E : Set (O → A.Sym) => |(μ (A.cyl O E)).toReal - (ν (A.cyl O E)).toReal|)
    (Set.finite_range _).bddAbove E

theorem dtv_le_of {O : Finset (Site d)} {μ ν : Measure A.Config} {c : ℝ}
    (h : ∀ E : Set (O → A.Sym), |(μ (A.cyl O E)).toReal - (ν (A.cyl O E)).toReal| ≤ c) :
    A.dtv O μ ν ≤ c :=
  ciSup_le h

theorem dtv_nonneg (O : Finset (Site d)) (μ ν : Measure A.Config) : 0 ≤ A.dtv O μ ν :=
  Real.iSup_nonneg (fun _ => abs_nonneg _)

theorem dtv_comm (O : Finset (Site d)) (μ ν : Measure A.Config) :
    A.dtv O μ ν = A.dtv O ν μ := by
  unfold dtv
  congr 1
  funext E
  exact abs_sub_comm _ _

theorem dtv_le_one (O : Finset (Site d)) (μ ν : Measure A.Config) [IsProbabilityMeasure μ]
    [IsProbabilityMeasure ν] : A.dtv O μ ν ≤ 1 := by
  refine A.dtv_le_of (fun E => ?_)
  rw [← measureReal_def, ← measureReal_def, abs_sub_le_iff]
  have h1 : μ.real (A.cyl O E) ≤ 1 := measureReal_le_one
  have h2 : ν.real (A.cyl O E) ≤ 1 := measureReal_le_one
  have h3 : 0 ≤ μ.real (A.cyl O E) := measureReal_nonneg
  have h4 : 0 ≤ ν.real (A.cyl O E) := measureReal_nonneg
  constructor <;> linarith

theorem deltaO_nonneg (ε : ℝ) (O : Finset (Site d)) (t : ℕ) : 0 ≤ A.deltaO ε O t :=
  Real.iSup_nonneg (fun _ => A.dtv_nonneg _ _ _)

theorem dtv_le_deltaO {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (O : Finset (Site d)) (t : ℕ)
    (x : A.Config) :
    A.dtv O (A.law ε (Measure.dirac x) t) (A.law ε (Measure.dirac A.zeroConfig) t) ≤
      A.deltaO ε O t := by
  refine le_ciSup (f := fun x : A.Config => A.dtv O (A.law ε (Measure.dirac x) t)
    (A.law ε (Measure.dirac A.zeroConfig) t)) ⟨1, ?_⟩ x
  rintro _ ⟨y, rfl⟩
  have := A.isProbabilityMeasure_law h0 h1 (Measure.dirac y) t
  have := A.isProbabilityMeasure_law h0 h1 (Measure.dirac A.zeroConfig) t
  exact A.dtv_le_one _ _ _

theorem deltaO_le_of {ε : ℝ} {O : Finset (Site d)} {t : ℕ} {c : ℝ}
    (h : ∀ x : A.Config,
      A.dtv O (A.law ε (Measure.dirac x) t) (A.law ε (Measure.dirac A.zeroConfig) t) ≤ c) :
    A.deltaO ε O t ≤ c :=
  ciSup_le h

/-! ## The coupling bound (NEW, for Lemma 8.5) -/

/-- Two events that agree off `D` have probabilities within `P(D)` (outer measure: `D` need not be
measurable). -/
theorem abs_toReal_sub_le_of_subset {α : Type*} [MeasurableSpace α] (P : Measure α)
    [IsProbabilityMeasure P] {S S' D : Set α} (h1 : S ⊆ S' ∪ D) (h2 : S' ⊆ S ∪ D) :
    |(P S).toReal - (P S').toReal| ≤ (P D).toReal := by
  have a : P S ≤ P S' + P D := (measure_mono h1).trans (measure_union_le _ _)
  have b : P S' ≤ P S + P D := (measure_mono h2).trans (measure_union_le _ _)
  have a' : (P S).toReal ≤ (P S').toReal + (P D).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) a
  have b' : (P S').toReal ≤ (P S).toReal + (P D).toReal := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _)]
    exact ENNReal.toReal_mono (ENNReal.add_ne_top.2 ⟨measure_ne_top _ _, measure_ne_top _ _⟩) b
  rw [abs_sub_le_iff]
  constructor <;> linarith

/-- The window probabilities from a point: `P_x(X_t ∈ cyl O ℰ)` is the noise probability of the
event `{ω : X_t(x, ω)|_O ∈ ℰ}`. -/
theorem law_dirac_cyl {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (x : A.Config) (t : ℕ)
    (O : Finset (Site d)) (E : Set (O → A.Sym)) :
    A.law ε (Measure.dirac x) t (A.cyl O E) =
      A.noiseLaw ε {ω | (fun w : O => A.run x ω t w.1) ∈ E} := by
  have hm : Measurable (fun ω : A.Noise => A.run x ω t) :=
    (A.measurable_run t).comp measurable_prodMk_left
  rw [A.law_dirac h0 h1, Measure.map_apply hm (A.measurableSet_cyl O E)]
  rfl

/-- **Coupling bound.** Driving two starts `x, y` by the same noise, the window total variation
distance at time `t` is at most the probability that the two trajectories disagree somewhere on
`O` at time `t`. -/
theorem dtv_law_dirac_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (x y : A.Config)
    (O : Finset (Site d)) (t : ℕ) :
    A.dtv O (A.law ε (Measure.dirac x) t) (A.law ε (Measure.dirac y) t) ≤
      (A.noiseLaw ε {ω | ∃ w ∈ O, A.run x ω t w ≠ A.run y ω t w}).toReal := by
  have := A.isProbabilityMeasure_noiseLaw h0 h1
  refine A.dtv_le_of (fun E => ?_)
  rw [A.law_dirac_cyl h0 h1, A.law_dirac_cyl h0 h1]
  have hagree : ∀ ω, ω ∉ {ω | ∃ w ∈ O, A.run x ω t w ≠ A.run y ω t w} →
      (fun w : O => A.run x ω t w.1) = (fun w : O => A.run y ω t w.1) := by
    intro ω hω
    funext w
    by_contra hne
    exact hω ⟨w.1, w.2, hne⟩
  refine abs_toReal_sub_le_of_subset _ (fun ω hω => ?_) (fun ω hω => ?_)
  · by_cases hD : ω ∈ {ω | ∃ w ∈ O, A.run x ω t w ≠ A.run y ω t w}
    · exact Or.inr hD
    · left
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rwa [← hagree ω hD]
  · by_cases hD : ω ∈ {ω | ∃ w ∈ O, A.run x ω t w ≠ A.run y ω t w}
    · exact Or.inr hD
    · left
      simp only [Set.mem_ofPred_eq] at hω ⊢
      rwa [hagree ω hD]

/-- `δ_O(t)` is at most the probability that some two starts disagree on `O` at time `t`. -/
theorem deltaO_le_disagree {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (O : Finset (Site d)) (t : ℕ) :
    A.deltaO ε O t ≤
      (A.noiseLaw ε {ω | ∃ x x' : A.Config, ∃ w ∈ O, A.run x ω t w ≠ A.run x' ω t w}).toReal := by
  have := A.isProbabilityMeasure_noiseLaw h0 h1
  refine A.deltaO_le_of (fun x => (A.dtv_law_dirac_le h0 h1 x A.zeroConfig O t).trans ?_)
  refine ENNReal.toReal_mono (measure_ne_top _ _) (measure_mono ?_)
  rintro ω ⟨w, hw, hne⟩
  exact ⟨x, A.zeroConfig, w, hw, hne⟩

/-- **Forgetting from coupling.** If on every finite window the probability that some two starts
disagree at time `t` tends to zero, the process forgets. -/
theorem forgets_of_coupling {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (hc : ∀ O : Finset (Site d), Tendsto (fun t => (A.noiseLaw ε
      {ω | ∃ x x' : A.Config, ∃ w ∈ O, A.run x ω t w ≠ A.run x' ω t w}).toReal) atTop (𝓝 0)) :
    A.Forgets ε := fun O =>
  squeeze_zero (fun t => A.deltaO_nonneg ε O t) (fun t => A.deltaO_le_disagree h0 h1 O t) (hc O)

end UND.CA

end
