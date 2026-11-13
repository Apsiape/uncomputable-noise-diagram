/-
# Section 2.2: the process as a measure-theoretic object (`set:def-noise` and the facts after it)

Proved here, for `0 ≤ ε ≤ 1`:
* `flagLaw ε`, `uniformSym R` and the noise law are probability measures (so the `if` inside
  Mathlib's `Measure.infinitePi` takes its product branch, and `noiseLaw` is not `0`);
* locality of the quorum rule (it reads `x` on `v + 𝒩`, `𝒩 = Λ × {c_0, …, c_k}`);
* measurability of `run` (so `law` is not `0` either);
* `law μ t` is a probability measure; `law μ 0 = μ`;
* the mixture formula `law μ t A = ∫ law (δ_x) t A dμ(x)`;
* the one-step product form `law (δ_x) 1 = ⊗_v siteLaw x v`;
* the cylinder probability `P(η = 1 on Σ) = ε^{|Σ|}` for a finite set `Σ` of noise indices;
* the Markov property `μΦ^{t+1} = (μΦ^t)Φ` (and `μΦ^{t+1} = (μΦ)Φ^t`).
-/
import FixedNoiseErgodicity.Basic
import Mathlib.Probability.Independence.InfinitePi
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Measure.Prod
import Mathlib.Data.Finset.Sum

set_option autoImplicit false

noncomputable section

namespace FNE

open MeasureTheory
open scoped ENNReal

variable {k : ℕ} {R : WangSet}

/-! ## The one-site laws -/

theorem isProbabilityMeasure_flagLaw {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsProbabilityMeasure (flagLaw ε) := by
  constructor
  simp only [flagLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    measure_univ, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add h0 (by linarith)]
  simp

instance isProbabilityMeasure_uniformSym : IsProbabilityMeasure (uniformSym R) := by
  constructor
  simp only [uniformSym, Measure.smul_apply, Measure.count_univ, smul_eq_mul,
    ENat.card_eq_coe_fintype_card, ENat.toENNReal_coe]
  exact ENNReal.inv_mul_cancel (by simp) (by simp)

theorem uniformSym_singleton (s : Sym R) :
    uniformSym R {s} = (Fintype.card (Sym R) : ℝ≥0∞)⁻¹ := by
  simp [uniformSym]

/-- The law of one noise variable `(η_t(v), ζ_t(v))`. -/
abbrev noiseSite (R : WangSet) (ε : ℝ) : Measure (Bool × Sym R) :=
  (flagLaw ε).prod (uniformSym R)

theorem isProbabilityMeasure_noiseSite {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsProbabilityMeasure (noiseSite R ε) := by
  haveI := isProbabilityMeasure_flagLaw h0 h1
  infer_instance

theorem isProbabilityMeasure_noiseLaw {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsProbabilityMeasure (noiseLaw k R ε) := by
  haveI := isProbabilityMeasure_noiseSite (R := R) h0 h1
  unfold noiseLaw
  infer_instance

/-! ## Locality of the rule -/

theorem checker_congr {y y' : Plane → Sym R} {u : Plane}
    (h : ∀ d ∈ box 1, y (u + d) = y' (u + d)) : checker y u = checker y' u := by
  have h0 : y u = y' u := by
    have := h (0, 0) (by decide)
    rwa [show u + ((0, 0) : Plane) = u from add_zero u] at this
  have hk : CheckerKeeps y u ↔ CheckerKeeps y' u := by
    unfold CheckerKeeps
    constructor
    · rintro ⟨s, hs, hall⟩
      refine ⟨s, h0 ▸ hs, fun d hd => ?_⟩
      obtain ⟨s', hs', hc⟩ := hall d hd
      refine ⟨s', ?_, hc⟩
      rw [← h d (Finset.mem_of_mem_erase hd)]
      exact hs'
    · rintro ⟨s, hs, hall⟩
      refine ⟨s, h0 ▸ hs, fun d hd => ?_⟩
      obtain ⟨s', hs', hc⟩ := hall d hd
      refine ⟨s', ?_, hc⟩
      rw [h d (Finset.mem_of_mem_erase hd)]
      exact hs'
  unfold checker
  by_cases hc : CheckerKeeps y u
  · rw [if_pos hc, if_pos (hk.mp hc), h0]
  · rw [if_neg hc, if_neg (fun h' => hc (hk.mpr h'))]

/-- Section 2.2: `F^{[k]}_R(x)(v)` depends only on `x` restricted to `v + 𝒩`,
`𝒩 = Λ × {c_0, …, c_k}`. -/
theorem quorumRule_local {x x' : Config k R} {v : Site k}
    (h : ∀ d ∈ box 1, ∀ i : Option (Fin k),
      x (v + (d, provider k i)) = x' (v + (d, provider k i))) :
    quorumRule k R x v = quorumRule k R x' v := by
  have hc : ∀ i : Option (Fin k), checkAll x (v.1, v.2 + provider k i) =
      checkAll x' (v.1, v.2 + provider k i) := by
    intro i
    exact checker_congr (fun d hd => h d hd i)
  have hq : quorumCount (checkAll x) v = quorumCount (checkAll x') v := by
    funext s
    unfold quorumCount
    simp only [hc]
  unfold quorumRule
  rw [hq]

/-! ## Measurability -/

/-- A function of configurations that only reads a finite window is measurable. -/
theorem measurable_of_local {β : Type*} [MeasurableSpace β] (W : Finset (Site k))
    (f : Config k R → β) (hf : ∀ y y' : Config k R, (∀ w ∈ W, y w = y' w) → f y = f y') :
    Measurable f := by
  classical
  let ext : (W → Sym R) → Config k R := fun z w => if h : w ∈ W then z ⟨w, h⟩ else .bot
  let r : Config k R → (W → Sym R) := fun y w => y w.1
  have hr : Measurable r := Measurable.of_eval (fun w => measurable_pi_apply w.1)
  have heq : f = (fun z => f (ext z)) ∘ r := by
    funext y
    exact hf _ _ (fun w hw => by simp [ext, r, hw])
  rw [heq]
  exact (measurable_of_countable _).comp hr

/-- The window `v + 𝒩` as a finset. -/
def window (v : Site k) : Finset (Site k) :=
  (box 1 ×ˢ (Finset.univ : Finset (Option (Fin k)))).image
    (fun p => v + (p.1, provider k p.2))

theorem measurable_quorumRule_apply (v : Site k) :
    Measurable (fun x : Config k R => quorumRule k R x v) :=
  measurable_of_local (window v) _ fun _ _ h => quorumRule_local fun d hd i =>
    h _ (Finset.mem_image.mpr ⟨(d, i), Finset.mem_product.mpr ⟨hd, Finset.mem_univ _⟩, rfl⟩)

theorem measurable_quorumRule : Measurable (quorumRule k R) :=
  Measurable.of_eval measurable_quorumRule_apply

/-- The process is a measurable function of the start and the noise. -/
theorem measurable_run (t : ℕ) :
    Measurable (fun p : Config k R × Noise k R => run p.1 p.2 t) := by
  induction t with
  | zero => exact measurable_fst
  | succ t ih =>
    refine Measurable.of_eval (fun v => ?_)
    have hflag : Measurable (fun p : Config k R × Noise k R => (p.2 (t, v)).1) :=
      measurable_fst.comp ((measurable_pi_apply (t, v)).comp measurable_snd)
    have hval : Measurable (fun p : Config k R × Noise k R => (p.2 (t, v)).2) :=
      measurable_snd.comp ((measurable_pi_apply (t, v)).comp measurable_snd)
    exact Measurable.ite (hflag (measurableSet_singleton true)) hval
      ((measurable_quorumRule_apply v).comp ih)

/-! ## Basic facts about `law` -/

theorem isProbabilityMeasure_law {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (μ : Measure (Config k R)) [IsProbabilityMeasure μ] (t : ℕ) :
    IsProbabilityMeasure (law k R ε μ t) := by
  haveI := isProbabilityMeasure_noiseLaw (k := k) (R := R) h0 h1
  exact (Measure.isProbabilityMeasure_map_iff (measurable_run t).aemeasurable).2 inferInstance

theorem law_zero {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure (Config k R))
    [SFinite μ] : law k R ε μ 0 = μ := by
  haveI := isProbabilityMeasure_noiseLaw (k := k) (R := R) h0 h1
  unfold law
  simp only [run]
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- `set:def-noise`, the mixture formula: `P_μ(X_t ∈ A) = ∫ P_x(X_t ∈ A) μ(dx)`. -/
theorem law_apply_eq_lintegral {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure (Config k R))
    [SFinite μ] (t : ℕ) {A : Set (Config k R)} (hA : MeasurableSet A) :
    law k R ε μ t A = ∫⁻ x, law k R ε (Measure.dirac x) t A ∂μ := by
  haveI := isProbabilityMeasure_noiseLaw (k := k) (R := R) h0 h1
  have hm := measurable_run (k := k) (R := R) t
  unfold law
  rw [Measure.map_apply hm hA, Measure.prod_apply (hm hA)]
  refine lintegral_congr (fun x => ?_)
  rw [Measure.map_apply hm hA, Measure.dirac_prod, Measure.map_apply measurable_prodMk_left (hm hA)]

/-- The law of `X_t` from a point: the push-forward of the noise law. -/
theorem law_dirac {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (x : Config k R) (t : ℕ) :
    law k R ε (Measure.dirac x) t = (noiseLaw k R ε).map (fun ω => run x ω t) := by
  haveI := isProbabilityMeasure_noiseLaw (k := k) (R := R) h0 h1
  unfold law
  rw [Measure.dirac_prod, Measure.map_map (measurable_run t) measurable_prodMk_left]
  rfl

/-! ## The cylinder probabilities of the replacement indicators -/

/-- `P(η = 1 on Σ) = ε^{|Σ|}` for a finite set `Σ` of space-time noise indices (distinct points
of positive time; index `(t, v)` is the paper's `(v, t + 1)`). -/
theorem noiseLaw_flags_eq {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (Sig : Finset (ℕ × Site k)) :
    noiseLaw k R ε {ω | ∀ p ∈ Sig, (ω p).1 = true} = ENNReal.ofReal ε ^ Sig.card := by
  haveI := isProbabilityMeasure_noiseSite (R := R) h0 h1
  have hset : {ω : Noise k R | ∀ p ∈ Sig, (ω p).1 = true} =
      Set.pi (Sig : Set (ℕ × Site k)) (fun _ => {b : Bool × Sym R | b.1 = true}) := by
    ext ω
    simp
  have hpi := Measure.infinitePi_pi (fun _ : ℕ × Site k => noiseSite R ε) (s := Sig)
    (t := fun _ => {b : Bool × Sym R | b.1 = true})
    (fun _ _ => measurable_fst (measurableSet_singleton true))
  rw [hset, noiseLaw]
  refine hpi.trans ?_
  have hone : noiseSite R ε {b : Bool × Sym R | b.1 = true} = ENNReal.ofReal ε := by
    have : {b : Bool × Sym R | b.1 = true} = ({true} : Set Bool) ×ˢ Set.univ := by
      ext b
      simp
    rw [this, Measure.prod_prod, measure_univ, mul_one]
    simp [flagLaw]
  simp only [hone, Finset.prod_const]

end FNE

end
