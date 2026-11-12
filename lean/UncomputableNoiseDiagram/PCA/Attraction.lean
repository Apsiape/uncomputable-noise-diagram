/-
# The PCA layer, part 8: time homogeneity and attraction (Lemma 8.5, second assertion)

Nodes P8 and the second half of F5 of `BLUEPRINT.md`, NEW. Lemma 8.5: "The failure event is
determined by a finite noise cone and decreases to probability zero. Time homogeneity makes its
probability the same all-start forward coupling bound. Existence of a stationary law follows from
Feller compactness as in Theorem 7.3. Coupling that stationary start to any initial law bounds
their finite-window total variation distance by the failure probability. This proves uniqueness
and attraction."

* `cone t W`: the finite set of sites read by `X_t` on `W` (`run_congr_cone`: the process on `W` at
  time `t` depends on the start only through `cone t W`);
* `disagree t O`: the forward coupling failure event (two starts differ on `O` at time `t`); it is
  a finite union of measurable events (`measurableSet_disagree`);
* time homogeneity: the noise from time `s` on, `tau s ω`, has the one-sided law
  (`noiseLaw₂_map_tau`), and `Ψ_{s,s+n} = run (tau s ω) n` (`flow_eq_run`), so the pullback failure
  event `pullFail j O` has the probability of `disagree j O` (`noiseLaw₂_pullFail`);
* the pullback failure events decrease (`pullFail_antitone`) to a null set when complete
  trajectories are almost surely unique, so their probabilities tend to zero;
* **`forgets_of_unique`**, **`ergodic_of_unique`**: almost surely unique complete trajectories give
  forgetting, hence ergodicity (a unique stationary law attracting every initial law), together
  with the pullback clause: Lemma 8.5.
-/
import UncomputableNoiseDiagram.PCA.Pullback

set_option autoImplicit false

noncomputable section

namespace UND.CA

open MeasureTheory Filter Topology
open scoped ENNReal

variable {d : ℕ} (A : CA d)

/-! ## The finite cone of dependence -/

/-- The sites read by `X_t` on `W`: `cone 0 W = W`, `cone (t+1) W = cone t (W + N_F)`. -/
def cone : ℕ → Finset (Site d) → Finset (Site d)
  | 0, W => W
  | t + 1, W => cone t (W.biUnion A.window)

/-- The process on `W` at time `t` depends on the start only through `cone t W`. -/
theorem run_congr_cone (ω : A.Noise) :
    ∀ (t : ℕ) (W : Finset (Site d)) (x x' : A.Config), (∀ v ∈ A.cone t W, x v = x' v) →
      ∀ w ∈ W, A.run x ω t w = A.run x' ω t w := by
  intro t
  induction t with
  | zero => exact fun W x x' h w hw => h w hw
  | succ t ih =>
    intro W x x' h w hw
    -- `X_{t+1}(w)` reads `X_t` on `w + N_F`
    have hprev : ∀ v ∈ W.biUnion A.window, A.run x ω t v = A.run x' ω t v :=
      ih (W.biUnion A.window) x x' h
    rw [run_succ, run_succ]
    simp only [update]
    split_ifs
    · rfl
    · exact A.apply_congr (fun z hz => hprev _ (Finset.mem_biUnion.mpr
        ⟨w, hw, Finset.mem_image.mpr ⟨z, hz, rfl⟩⟩))

/-- The forward coupling failure event: two starts differ on `O` at time `t`. -/
def disagree (t : ℕ) (O : Finset (Site d)) : Set A.Noise :=
  {ω | ∃ x x' : A.Config, ∃ w ∈ O, A.run x ω t w ≠ A.run x' ω t w}

/-- The forward coupling failure event is measurable: it is a finite union over patterns on the
cone of measurable events. -/
theorem measurableSet_disagree (t : ℕ) (O : Finset (Site d)) :
    MeasurableSet (A.disagree t O) := by
  classical
  let W := A.cone t O
  let ext : (W → A.Sym) → A.Config := fun z v => if h : v ∈ W then z ⟨v, h⟩ else
    ⟨0, A.numSymbols_pos⟩
  have heq : A.disagree t O = ⋃ (p : W → A.Sym) (p' : W → A.Sym) (w : O),
      {ω | A.run (ext p) ω t w.1 ≠ A.run (ext p') ω t w.1} := by
    ext ω
    simp only [disagree, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨x, x', w, hw, hne⟩
      refine ⟨fun v => x v.1, fun v => x' v.1, ⟨w, hw⟩, ?_⟩
      have h1 := A.run_congr_cone ω t O x (ext fun v => x v.1)
        (fun v hv => by simp [ext, W, hv]) w hw
      have h2 := A.run_congr_cone ω t O x' (ext fun v => x' v.1)
        (fun v hv => by simp [ext, W, hv]) w hw
      rwa [← h1, ← h2]
    · rintro ⟨p, p', w, hne⟩
      exact ⟨ext p, ext p', w.1, w.2, hne⟩
  rw [heq]
  refine MeasurableSet.iUnion fun p => MeasurableSet.iUnion fun p' => MeasurableSet.iUnion
    fun w => ?_
  have hm : ∀ y : A.Config, Measurable (fun ω : A.Noise => A.run y ω t w.1) := fun y =>
    (measurable_pi_apply w.1).comp ((A.measurable_run t).comp measurable_prodMk_left)
  exact (measurableSet_eq_fun (hm _) (hm _)).compl

/-! ## Time homogeneity of the two-sided noise -/

/-- The noise from time `s` on, as a one-sided noise: `tau s ω (t, w) = ω (s + t + 1, w)`. -/
def tau (s : ℤ) (ω : A.Noise₂) : A.Noise := fun p => ω (s + p.1 + 1, p.2)

theorem measurable_tau (s : ℤ) : Measurable (A.tau s) :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

/-- Time homogeneity: the noise from any time on has the law of the one-sided noise. -/
theorem noiseLaw₂_map_tau {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (s : ℤ) :
    (A.noiseLaw₂ ε).map (A.tau s) = A.noiseLaw ε := by
  have := A.isProbabilityMeasure_noiseSite h0 h1
  have hinj : Function.Injective (fun p : ℕ × Site d => (s + (p.1 : ℤ) + 1, p.2)) := by
    rintro ⟨t, v⟩ ⟨t', v'⟩ h
    simp only [Prod.mk.injEq] at h
    obtain ⟨h1, h2⟩ := h
    have : t = t' := by omega
    rw [this, h2]
  exact Measure.map_infinitePi_infinitePi_of_inj hinj

/-- `Ψ_{s,s+n}(x)` is the process from `x` driven by the noise from time `s` on. -/
theorem flow_eq_run (ω : A.Noise₂) (s : ℤ) (n : ℕ) (x : A.Config) :
    A.flow ω s n x = A.run x (A.tau s ω) n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    show A.update (fun w => ω (s + (n : ℤ) + 1, w)) (A.flow ω s n x) =
      A.update (fun w => A.tau s ω (n, w)) (A.run x (A.tau s ω) n)
    rw [ih]
    rfl

/-- The pullback failure event at depth `j` on the window `O`. -/
def pullFail (j : ℕ) (O : Finset (Site d)) : Set A.Noise₂ :=
  {ω | ∃ x x' : A.Config, ∃ w ∈ O, A.pullback ω j x w ≠ A.pullback ω j x' w}

theorem pullFail_eq_preimage (j : ℕ) (O : Finset (Site d)) :
    A.pullFail j O = A.tau (-(j : ℤ)) ⁻¹' A.disagree j O := by
  ext ω
  simp only [pullFail, disagree, Set.mem_preimage, Set.mem_ofPred_eq, pullback, flow_eq_run]

theorem measurableSet_pullFail (j : ℕ) (O : Finset (Site d)) :
    MeasurableSet (A.pullFail j O) := by
  rw [A.pullFail_eq_preimage]
  exact A.measurable_tau _ (A.measurableSet_disagree j O)

/-- Time homogeneity: the pullback failure probability is the forward coupling failure
probability. -/
theorem noiseLaw₂_pullFail {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (j : ℕ) (O : Finset (Site d)) :
    A.noiseLaw₂ ε (A.pullFail j O) = A.noiseLaw ε (A.disagree j O) := by
  rw [A.pullFail_eq_preimage, ← Measure.map_apply (A.measurable_tau _)
    (A.measurableSet_disagree j O), A.noiseLaw₂_map_tau h0 h1]

/-- The pullback failure events decrease in the depth (the images are nested). -/
theorem pullFail_antitone (O : Finset (Site d)) : Antitone (fun j => A.pullFail j O) := by
  intro j j' hjj' ω hω
  obtain ⟨x, x', w, hw, hne⟩ := hω
  obtain ⟨y, hy⟩ := A.pullback_mono ω hjj' x
  obtain ⟨y', hy'⟩ := A.pullback_mono ω hjj' x'
  exact ⟨y, y', w, hw, by rwa [← hy, ← hy']⟩

/-! ## Lemma 8.5 -/

/-- **Lemma 8.5, attraction.** If complete common-noise trajectories are almost surely unique,
the process forgets: the forward coupling failure probability on every window tends to zero. -/
theorem forgets_of_unique {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (h : ∀ᵐ ω ∂(A.noiseLaw₂ ε), ∀ X Y : ℤ → A.Config, A.IsComplete ω X → A.IsComplete ω Y →
      X 0 = Y 0) :
    A.Forgets ε := by
  have := A.isProbabilityMeasure_noiseLaw₂ h0 h1
  refine A.forgets_of_coupling h0 h1 (fun O => ?_)
  -- the failure events decrease to a null set
  have hnull : A.noiseLaw₂ ε (⋂ j, A.pullFail j O) = 0 := by
    refine measure_mono_null (fun ω hω => ?_) (ae_iff.mp h)
    intro hgood
    obtain ⟨j₀, hj₀⟩ := A.pullback_eventually_singleton_of_unique ω O
      (fun X Y hX hY w _ => congrFun (hgood X Y hX hY) w)
    obtain ⟨x, x', w, hw, hne⟩ := Set.mem_iInter.mp hω j₀
    exact hne (hj₀ j₀ le_rfl x x' w hw)
  have hlim : Tendsto (fun j => A.noiseLaw₂ ε (A.pullFail j O)) atTop (𝓝 0) := by
    rw [← hnull]
    exact tendsto_measure_iInter_atTop
      (fun j => (A.measurableSet_pullFail j O).nullMeasurableSet) (A.pullFail_antitone O)
      ⟨0, measure_ne_top _ _⟩
  have hlim' : Tendsto (fun j => A.noiseLaw ε (A.disagree j O)) atTop (𝓝 0) := by
    simpa only [A.noiseLaw₂_pullFail h0 h1] using hlim
  have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hlim'
  rw [ENNReal.toReal_zero] at this
  exact this

/-- **Lemma 8.5.** If complete common-noise trajectories are almost surely unique, then the PCA
is ergodic (a unique stationary law attracting every initial law) and every finite-window
pullback image is almost surely eventually a singleton. -/
theorem ergodic_of_unique {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (h : ∀ᵐ ω ∂(A.noiseLaw₂ ε), ∀ X Y : ℤ → A.Config, A.IsComplete ω X → A.IsComplete ω Y →
      X 0 = Y 0) :
    A.IsErgodic ε ∧ A.PullbackEventuallySingleton ε :=
  ⟨(A.ergodic_of_forgets h0 h1 (A.forgets_of_unique h0 h1 h)).1,
    A.pullbackEventuallySingleton_of_unique h⟩

end UND.CA

end
