/-
# The PCA layer, part 2: the one-step product form and the Markov property

Node P3 of `BLUEPRINT.md` (Part A.1). Ported from the forgetting core
(`FixedNoiseErgodicity/Section2/Markov.lean`, same authors, v4.35 version), from its quorum rule
to an arbitrary cellular automaton `A : CA d` (decision D3); the step `FNE.step x ζ` is our
`A.update ζ x`. Proofs follow the originals.

* the noise splits into its first time slice and the shifted rest, independent, with laws
  `sliceLaw` and `noiseLaw` (`noiseLaw_map_splitN`);
* `law (δ_x) 1 = ⊗_w ((1 - ε) δ_{F(x)(w)} + ε · uniform)` (`law_dirac_one`): uniform whole-symbol
  replacement is a positive-rate PCA (`siteLaw_pos`);
* the Markov property `μ F_ε^{t+1} = (μ F_ε^t) F_ε` (`law_succ`) and
  `μ F_ε^{t+1} = (μ F_ε) F_ε^t` (`law_succ'`).
-/
import UncomputableNoiseDiagram.PCA.Process

set_option autoImplicit false

noncomputable section

namespace UND.CA

open MeasureTheory
open scoped ENNReal

variable {d : ℕ} (A : CA d)

/-! ## The first time slice and the rest of the noise -/

/-- The first time slice of the noise: `w ↦ (E_1(w), Z_1(w))`. -/
def slice0 (ω : A.Noise) : Site d → Bool × A.Sym := fun w => ω (0, w)

/-- The noise after the first step, shifted back by one unit of time. -/
def shiftN (ω : A.Noise) : A.Noise := fun p => ω (p.1 + 1, p.2)

/-- The split of the noise into its first slice and the rest. -/
def splitN (ω : A.Noise) : (Site d → Bool × A.Sym) × A.Noise := (A.slice0 ω, A.shiftN ω)

theorem run_succ (x : A.Config) (ω : A.Noise) (t : ℕ) :
    A.run x ω (t + 1) = A.update (fun w => ω (t, w)) (A.run x ω t) := rfl

theorem run_one (x : A.Config) (ω : A.Noise) : A.run x ω 1 = A.update (A.slice0 ω) x := rfl

theorem run_succ_shift (x : A.Config) (ω : A.Noise) (t : ℕ) :
    A.run x ω (t + 1) = A.run (A.run x ω 1) (A.shiftN ω) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    rw [run_succ A x ω (t + 1), run_succ A (A.run x ω 1) (A.shiftN ω) t, ← ih]
    rfl

theorem measurable_slice0 : Measurable A.slice0 :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

theorem measurable_shiftN : Measurable A.shiftN :=
  Measurable.of_eval (fun _ => measurable_pi_apply _)

theorem measurable_splitN : Measurable A.splitN :=
  A.measurable_slice0.prodMk A.measurable_shiftN

theorem measurable_update :
    Measurable (fun q : A.Config × (Site d → Bool × A.Sym) => A.update q.2 q.1) := by
  refine Measurable.of_eval (fun w => ?_)
  have hflag : Measurable (fun q : A.Config × (Site d → Bool × A.Sym) => (q.2 w).1) :=
    measurable_fst.comp ((measurable_pi_apply w).comp measurable_snd)
  have hval : Measurable (fun q : A.Config × (Site d → Bool × A.Sym) => (q.2 w).2) :=
    measurable_snd.comp ((measurable_pi_apply w).comp measurable_snd)
  exact Measurable.ite (hflag (measurableSet_singleton true)) hval
    ((A.measurable_apply_apply w).comp measurable_fst)

/-- The law of one time slice of the noise. -/
abbrev sliceLaw (ε : ℝ) : Measure (Site d → Bool × A.Sym) :=
  Measure.infinitePi (fun _ : Site d => A.noiseSite ε)

/-- Reindexing `Site ⊕ (ℕ × Site) → ℕ × Site`: `inl w ↦ (0, w)`, `inr (t, w) ↦ (t + 1, w)`. -/
def splitIdx : Site d ⊕ (ℕ × Site d) → ℕ × Site d
  | .inl w => (0, w)
  | .inr p => (p.1 + 1, p.2)

theorem splitIdx_injective : Function.Injective (splitIdx (d := d)) := by
  rintro (v | ⟨t, v⟩) (v' | ⟨t', v'⟩) h <;> simp_all [splitIdx]

/-- The first time slice and the rest of the noise are independent, with laws `sliceLaw` and
`noiseLaw`. -/
theorem noiseLaw_map_splitN {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (A.noiseLaw ε).map A.splitN = (A.sliceLaw ε).prod (A.noiseLaw ε) := by
  have := A.isProbabilityMeasure_noiseSite h0 h1
  have := A.isProbabilityMeasure_noiseLaw h0 h1
  let E := MeasurableEquiv.sumPiEquivProdPi (fun _ : Site d ⊕ (ℕ × Site d) => Bool × A.Sym)
  have hsum : ((A.sliceLaw ε).prod (A.noiseLaw ε)).map E.symm =
      Measure.infinitePi (fun _ : Site d ⊕ (ℕ × Site d) => A.noiseSite ε) := by
    refine Measure.eq_infinitePi _ (fun s t ht => ?_)
    rw [Measure.map_apply E.symm.measurable
      (MeasurableSet.pi s.countable_toSet (fun i _ => ht i))]
    have hpre : E.symm ⁻¹' (Set.pi (s : Set (Site d ⊕ (ℕ × Site d))) t) =
        (Set.pi (s.toLeft : Set (Site d)) (fun v => t (.inl v))) ×ˢ
          (Set.pi (s.toRight : Set (ℕ × Site d)) (fun p => t (.inr p))) := by
      ext ⟨f, g⟩
      simp [E, MeasurableEquiv.coe_sumPiEquivProdPi_symm, Set.mem_pi, Sum.forall]
    rw [hpre, Measure.prod_prod, sliceLaw, noiseLaw,
      Measure.infinitePi_pi _ (fun i _ => ht (.inl i)),
      Measure.infinitePi_pi _ (fun i _ => ht (.inr i))]
    conv_rhs => rw [← Finset.toLeft_disjSum_toRight (u := s)]
    rw [Finset.prod_disjSum]
  have hre : Measurable (fun (ω : A.Noise) (i : Site d ⊕ (ℕ × Site d)) => ω (splitIdx i)) :=
    Measurable.of_eval (fun _ => measurable_pi_apply _)
  have h2 : (A.noiseLaw ε).map (fun ω i => ω (splitIdx i)) =
      Measure.infinitePi (fun _ : Site d ⊕ (ℕ × Site d) => A.noiseSite ε) :=
    Measure.map_infinitePi_infinitePi_of_inj splitIdx_injective
  have hcomp : (A.splitN : A.Noise → _) = E ∘ (fun ω i => ω (splitIdx i)) := by
    funext ω
    rfl
  rw [hcomp, ← Measure.map_map E.measurable hre, h2, ← hsum,
    Measure.map_map E.measurable E.symm.measurable, MeasurableEquiv.self_comp_symm,
    Measure.map_id]

theorem noiseLaw_map_slice0 {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (A.noiseLaw ε).map A.slice0 = A.sliceLaw ε := by
  have := A.isProbabilityMeasure_noiseLaw h0 h1
  have : (A.noiseLaw ε).map A.slice0 = ((A.noiseLaw ε).map A.splitN).map Prod.fst := by
    rw [Measure.map_map measurable_fst A.measurable_splitN]
    rfl
  rw [this, A.noiseLaw_map_splitN h0 h1, Measure.map_fst_prod, measure_univ, one_smul]

/-! ## The one-step product form -/

/-- Section 2: the law of `X_{t+1}(w)` given `X_t = x`: `(1 - ε) δ_{F(x)(w)} + ε · uniform`. -/
def siteLaw (ε : ℝ) (x : A.Config) (w : Site d) : Measure A.Sym :=
  ENNReal.ofReal (1 - ε) • Measure.dirac (A.apply x w) + ENNReal.ofReal ε • A.uniformLaw

/-- The image of the one-site noise law under `(b, s) ↦ (b ? s : a)` is
`(1 - ε) δ_a + ε · uniform`. -/
theorem noiseSite_map_eq {ε : ℝ} (a : A.Sym) :
    (A.noiseSite ε).map (fun b : Bool × A.Sym => if b.1 then b.2 else a) =
      ENNReal.ofReal (1 - ε) • Measure.dirac a + ENNReal.ofReal ε • A.uniformLaw := by
  have hg : Measurable (fun b : Bool × A.Sym => if b.1 then b.2 else a) :=
    measurable_of_countable _
  rw [noiseSite, FNE.flagLaw, Measure.add_prod, Measure.prod_smul_left, Measure.prod_smul_left,
    Measure.dirac_prod, Measure.dirac_prod, Measure.map_add _ _ hg,
    (Measure.map_smul _ hg.aemeasurable), (Measure.map_smul _ hg.aemeasurable),
    Measure.map_map hg measurable_prodMk_left, Measure.map_map hg measurable_prodMk_left]
  have e1 : ((fun b : Bool × A.Sym => if b.1 then b.2 else a) ∘ Prod.mk true) = id := by
    funext s
    rfl
  have e2 : ((fun b : Bool × A.Sym => if b.1 then b.2 else a) ∘ Prod.mk false) =
      fun _ => a := by
    funext s
    rfl
  rw [e1, e2, Measure.map_id, Measure.map_const, measure_univ, one_smul, add_comm]

/-- **Section 2, the displayed update in law.** Given `X_0 = x`, the values `X_1(w)` are
independent with laws `(1 - ε) δ_{F(x)(w)} + ε · uniform`. -/
theorem law_dirac_one {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (x : A.Config) :
    A.law ε (Measure.dirac x) 1 = Measure.infinitePi (fun w => A.siteLaw ε x w) := by
  have := A.isProbabilityMeasure_noiseSite h0 h1
  have hg : ∀ w : Site d,
      Measurable (fun b : Bool × A.Sym => if b.1 then b.2 else A.apply x w) :=
    fun _ => measurable_of_countable _
  have key := Measure.infinitePi_map_pi (fun _ : Site d => A.noiseSite ε)
    (f := fun w (b : Bool × A.Sym) => if b.1 then b.2 else A.apply x w) hg
  have hgm : Measurable (fun (ζ : Site d → Bool × A.Sym) w =>
      if (ζ w).1 then (ζ w).2 else A.apply x w) :=
    Measurable.of_eval (fun w => (hg w).comp (measurable_pi_apply w))
  rw [A.law_dirac h0 h1]
  have e : (fun ω : A.Noise => A.run x ω 1) = (fun (ζ : Site d → Bool × A.Sym) w =>
      if (ζ w).1 then (ζ w).2 else A.apply x w) ∘ A.slice0 := by
    funext ω
    rfl
  rw [e, ← Measure.map_map hgm A.measurable_slice0, A.noiseLaw_map_slice0 h0 h1]
  refine key.trans ?_
  congr 1
  funext w
  exact A.noiseSite_map_eq _

/-! ## The Markov property -/

/-- `μ F^{t+1} = (μ F) F^t`: the process after one step is the process from `X_1`. -/
theorem law_succ' {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (μ : Measure A.Config)
    [IsProbabilityMeasure μ] (t : ℕ) :
    A.law ε μ (t + 1) = A.law ε (A.law ε μ 1) t := by
  have := A.isProbabilityMeasure_noiseLaw h0 h1
  have := A.isProbabilityMeasure_noiseSite h0 h1
  have hrun := A.measurable_run t
  have hstep := A.measurable_update
  let H : (A.Config × (Site d → Bool × A.Sym)) × A.Noise → A.Config :=
    fun q => A.run (A.update q.1.2 q.1.1) q.2 t
  have hH : Measurable H := hrun.comp ((hstep.comp measurable_fst).prodMk measurable_snd)
  let G : A.Config × ((Site d → Bool × A.Sym) × A.Noise) → A.Config :=
    fun z => A.run (A.update z.2.1 z.1) z.2.2 t
  have hG : Measurable G :=
    hrun.comp ((hstep.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).prodMk
      (measurable_snd.comp measurable_snd))
  -- the left side
  have hL : A.law ε μ (t + 1) =
      ((μ.prod (A.sliceLaw ε)).prod (A.noiseLaw ε)).map H := by
    have e1 : (fun p : A.Config × A.Noise => A.run p.1 p.2 (t + 1)) =
        G ∘ Prod.map id A.splitN := by
      funext p
      simp only [Function.comp_apply, Prod.map_fst, Prod.map_snd, id_eq, G]
      rw [run_succ_shift, run_one]
      rfl
    have hPM := Measure.map_prod_map μ (A.noiseLaw ε) measurable_id A.measurable_splitN
    rw [Measure.map_id, A.noiseLaw_map_splitN h0 h1] at hPM
    unfold law
    rw [e1, ← Measure.map_map hG (measurable_id.prodMap A.measurable_splitN), ← hPM,
      ← Measure.prodAssoc_prod, Measure.map_map hG MeasurableEquiv.prodAssoc.measurable]
    rfl
  -- the right side
  have hS : A.law ε μ 1 = (μ.prod (A.sliceLaw ε)).map (fun q => A.update q.2 q.1) := by
    have hPM := Measure.map_prod_map μ (A.noiseLaw ε) measurable_id A.measurable_slice0
    rw [Measure.map_id, A.noiseLaw_map_slice0 h0 h1] at hPM
    unfold law
    rw [hPM, Measure.map_map hstep (measurable_id.prodMap A.measurable_slice0)]
    rfl
  have hPM2 := Measure.map_prod_map (μ.prod (A.sliceLaw ε)) (A.noiseLaw ε) hstep measurable_id
  rw [Measure.map_id] at hPM2
  rw [hL, hS]
  unfold law
  rw [hPM2, Measure.map_map hrun (hstep.prodMap measurable_id)]
  rfl

/-- **The Markov property** (Section 2): `μ F^{t+1} = (μ F^t) F`. -/
theorem law_succ {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    ∀ (t : ℕ) (μ : Measure A.Config) [IsProbabilityMeasure μ],
      A.law ε μ (t + 1) = A.law ε (A.law ε μ t) 1 := by
  intro t
  induction t with
  | zero =>
    intro μ _
    rw [A.law_zero h0 h1]
  | succ t ih =>
    intro μ _
    have := A.isProbabilityMeasure_law h0 h1 μ 1
    have := A.isProbabilityMeasure_law h0 h1 μ (t + 1)
    rw [A.law_succ' h0 h1 μ (t + 1), ih (A.law ε μ 1), ← A.law_succ' h0 h1 μ t]

/-- Positive rates (Section 2: "Independent replacement gives every symbol positive probability
at every update"): for `ε > 0`, every symbol has probability at least `ε / |Σ| > 0` under every
`siteLaw x w`. -/
theorem siteLaw_pos {ε : ℝ} (hε : 0 < ε) (x : A.Config) (w : Site d) (s : A.Sym) :
    0 < A.siteLaw ε x w {s} := by
  have h1 : 0 < ENNReal.ofReal ε * A.uniformLaw {s} := by
    rw [uniformLaw_singleton]
    exact ENNReal.mul_pos (ENNReal.ofReal_pos.mpr hε).ne' (ENNReal.inv_ne_zero.mpr (by simp))
  refine lt_of_lt_of_le h1 ?_
  simp only [siteLaw, Measure.coe_add, Measure.coe_smul, Pi.add_apply, Pi.smul_apply,
    smul_eq_mul]
  exact le_add_self

end UND.CA

end
