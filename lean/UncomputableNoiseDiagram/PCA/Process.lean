/-
# The PCA layer, part 1: noise laws, locality, measurability, basic facts about `law`

Nodes P1 and P2 of `BLUEPRINT.md` (Part A.1). Ported from the forgetting core
(`FixedNoiseErgodicity/Section2/Process.lean`, same authors; the ported v4.35 version under
`/opt/forgetting-arxiv-2026-11-10/project`), from its quorum rule `quorumRule k R` on `ℤ² × ℤᵏ` to
an arbitrary cellular automaton `A : CA d` (decision D3). Proofs follow the originals line by
line; the default symbol of `measurable_of_local` is `0 : Fin |Σ|` instead of `⊥`.

* P1: `isProbabilityMeasure_uniformLaw`, `isProbabilityMeasure_noiseSite`,
  `isProbabilityMeasure_noiseLaw`, `isProbabilityMeasure_noiseLaw₂` (`0 ≤ ε ≤ 1`);
* P2: locality of `A.apply` on `w + N_F` (`apply_congr`), measurability of functions reading a
  finite window (`measurable_of_local`), of `A.apply` and of `A.run`; `law` is a probability
  measure, `law μ 0 = μ`, the mixture formula `law μ t A = ∫ law (δ_x) t A dμ(x)`,
  `law (δ_x) t` = image of the noise law; the flag cylinders `P(E = 1 on Σ) = ε^{|Σ|}`.
-/
import UncomputableNoiseDiagram.Statements
import FixedNoiseErgodicity.Section2.Process

set_option autoImplicit false

noncomputable section

namespace UND.CA

open MeasureTheory
open scoped ENNReal

variable {d : ℕ} (A : CA d)

/-! ## P1: the one-site laws and the noise laws -/

instance isProbabilityMeasure_uniformLaw : IsProbabilityMeasure A.uniformLaw := by
  constructor
  simp only [uniformLaw, Measure.smul_apply, Measure.count_univ, smul_eq_mul,
    ENat.card_eq_coe_fintype_card, ENat.toENNReal_coe, Fintype.card_fin]
  exact ENNReal.inv_mul_cancel (by simpa using A.numSymbols_pos.ne') (by simp)

theorem uniformLaw_singleton (s : A.Sym) : A.uniformLaw {s} = (A.numSymbols : ℝ≥0∞)⁻¹ := by
  simp [uniformLaw]

/-- The law of one noise variable `(E_t(w), Z_t(w))`. -/
abbrev noiseSite (ε : ℝ) : Measure (Bool × A.Sym) := (FNE.flagLaw ε).prod A.uniformLaw

theorem isProbabilityMeasure_noiseSite {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsProbabilityMeasure (A.noiseSite ε) := by
  have := FNE.isProbabilityMeasure_flagLaw h0 h1
  infer_instance

theorem isProbabilityMeasure_noiseLaw {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsProbabilityMeasure (A.noiseLaw ε) := by
  have := A.isProbabilityMeasure_noiseSite h0 h1
  unfold noiseLaw
  infer_instance

theorem isProbabilityMeasure_noiseLaw₂ {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsProbabilityMeasure (A.noiseLaw₂ ε) := by
  have := A.isProbabilityMeasure_noiseSite h0 h1
  unfold noiseLaw₂
  infer_instance

/-! ## P2: locality and measurability -/

/-- Section 2: `F(x)(w)` depends only on `x` restricted to `w + N_F`. -/
theorem apply_congr {x x' : A.Config} {w : Site d} (h : ∀ z ∈ A.nbhd, x (w + z) = x' (w + z)) :
    A.apply x w = A.apply x' w := by
  unfold apply
  congr 1
  funext z
  exact h z.1 z.2

/-- The window `w + N_F` as a finset. -/
def window (w : Site d) : Finset (Site d) := A.nbhd.image (fun z => w + z)

/-- A function of configurations that only reads a finite window is measurable. -/
theorem measurable_of_local {β : Type*} [MeasurableSpace β] (W : Finset (Site d))
    (f : A.Config → β) (hf : ∀ y y' : A.Config, (∀ w ∈ W, y w = y' w) → f y = f y') :
    Measurable f := by
  classical
  let ext : (W → A.Sym) → A.Config := fun z w => if h : w ∈ W then z ⟨w, h⟩ else
    ⟨0, A.numSymbols_pos⟩
  let r : A.Config → (W → A.Sym) := fun y w => y w.1
  have hr : Measurable r := Measurable.of_eval (fun w => measurable_pi_apply w.1)
  have heq : f = (fun z => f (ext z)) ∘ r := by
    funext y
    exact hf _ _ (fun w hw => by simp [ext, r, hw])
  rw [heq]
  exact (measurable_of_countable _).comp hr

theorem measurable_apply_apply (w : Site d) : Measurable (fun x : A.Config => A.apply x w) :=
  A.measurable_of_local (A.window w) _ fun _ _ h => A.apply_congr fun z hz =>
    h _ (Finset.mem_image.mpr ⟨z, hz, rfl⟩)

theorem measurable_apply : Measurable A.apply :=
  Measurable.of_eval A.measurable_apply_apply

/-- The process is a measurable function of the start and the noise. -/
theorem measurable_run (t : ℕ) :
    Measurable (fun p : A.Config × A.Noise => A.run p.1 p.2 t) := by
  induction t with
  | zero => exact measurable_fst
  | succ t ih =>
    refine Measurable.of_eval (fun w => ?_)
    have hflag : Measurable (fun p : A.Config × A.Noise => (p.2 (t, w)).1) :=
      measurable_fst.comp ((measurable_pi_apply (t, w)).comp measurable_snd)
    have hval : Measurable (fun p : A.Config × A.Noise => (p.2 (t, w)).2) :=
      measurable_snd.comp ((measurable_pi_apply (t, w)).comp measurable_snd)
    exact Measurable.ite (hflag (measurableSet_singleton true)) hval
      ((A.measurable_apply_apply w).comp ih)

/-! ## P2: basic facts about `law` -/

theorem isProbabilityMeasure_law {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (μ : Measure A.Config) [IsProbabilityMeasure μ] (t : ℕ) :
    IsProbabilityMeasure (A.law ε μ t) := by
  have := A.isProbabilityMeasure_noiseLaw h0 h1
  exact (Measure.isProbabilityMeasure_map_iff (A.measurable_run t).aemeasurable).2 inferInstance

theorem law_zero {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure A.Config) [SFinite μ] :
    A.law ε μ 0 = μ := by
  have := A.isProbabilityMeasure_noiseLaw h0 h1
  unfold law
  simp only [run]
  rw [Measure.map_fst_prod, measure_univ, one_smul]

/-- Section 2, the mixture formula: `P_μ(X_t ∈ B) = ∫ P_x(X_t ∈ B) μ(dx)`. -/
theorem law_apply_eq_lintegral {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure A.Config)
    [SFinite μ] (t : ℕ) {B : Set A.Config} (hB : MeasurableSet B) :
    A.law ε μ t B = ∫⁻ x, A.law ε (Measure.dirac x) t B ∂μ := by
  have := A.isProbabilityMeasure_noiseLaw h0 h1
  have hm := A.measurable_run t
  unfold law
  rw [Measure.map_apply hm hB, Measure.prod_apply (hm hB)]
  refine lintegral_congr (fun x => ?_)
  rw [Measure.map_apply hm hB, Measure.dirac_prod, Measure.map_apply measurable_prodMk_left (hm hB)]

/-- The law of `X_t` from a point: the push-forward of the noise law. -/
theorem law_dirac {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (x : A.Config) (t : ℕ) :
    A.law ε (Measure.dirac x) t = (A.noiseLaw ε).map (fun ω => A.run x ω t) := by
  have := A.isProbabilityMeasure_noiseLaw h0 h1
  unfold law
  rw [Measure.dirac_prod, Measure.map_map (A.measurable_run t) measurable_prodMk_left]
  rfl

/-! ## The cylinder probabilities of the replacement flags -/

/-- `P(E = 1 on Σ) = ε^{|Σ|}` for a finite set `Σ` of noise indices. -/
theorem noiseLaw_flags_eq {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (Sig : Finset (ℕ × Site d)) :
    A.noiseLaw ε {ω | ∀ p ∈ Sig, (ω p).1 = true} = ENNReal.ofReal ε ^ Sig.card := by
  have := A.isProbabilityMeasure_noiseSite h0 h1
  have hset : {ω : A.Noise | ∀ p ∈ Sig, (ω p).1 = true} =
      Set.pi (Sig : Set (ℕ × Site d)) (fun _ => {b : Bool × A.Sym | b.1 = true}) := by
    ext ω
    simp
  have hpi := Measure.infinitePi_pi (fun _ : ℕ × Site d => A.noiseSite ε) (s := Sig)
    (t := fun _ => {b : Bool × A.Sym | b.1 = true})
    (fun _ _ => measurable_fst (measurableSet_singleton true))
  rw [hset, noiseLaw]
  refine hpi.trans ?_
  have hone : A.noiseSite ε {b : Bool × A.Sym | b.1 = true} = ENNReal.ofReal ε := by
    have : {b : Bool × A.Sym | b.1 = true} = ({true} : Set Bool) ×ˢ Set.univ := by
      ext b
      simp
    rw [this, Measure.prod_prod, measure_univ, mul_one]
    simp [FNE.flagLaw]
  simp only [hone, Finset.prod_const]

end UND.CA

end
