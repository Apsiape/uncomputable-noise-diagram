/-
# Section 7: the initial law, its translation invariance and its evolution (Mem1, second part)

Part of node Mem1 of `BLUEPRINT.md` (Part A.7), NEW (D42; QB s9: the time-0 law built from the
chart law must be translation invariant, as the initial law of Theorem 7.3).

Paper (Section 7): "… Initialize each helper by its ideal chart-driven copying process with
independent negative-time noise. … Spatially average the joint chart/helper law; its phase is Haar
and typical almost surely. The positive-time noise is independent of this initial law."

Formalization (generic in the chart parameter space `Θ` with a law `P`):
* **`measurable_X0`**: the time-0 configuration is measurable in (chart parameter, negative-time
  noise) when the chart symbols are; **`X0_shift`**: it is translation covariant;
* `initLaw P cSf ε` (the push-forward of `P ⊗ noise` along `X0`), `isProbabilityMeasure_initLaw`,
  **`initLaw_TI`** (translation invariance from a covariance of the chart parameter preserving
  `P` and the translation invariance of the noise law);
* `glue` (a negative-time and a positive-time noise make a two-sided noise), `negPart_glue`,
  `posPart_glue`, **`glue_law`** (`(noise ⊗ noise).map glue` is the two-sided noise law, by
  `Measure.eq_infinitePi` on boxes);
* `encode_hyb` (the hybrid trajectory at time `t ≥ 0` is the automaton run from `X0`),
  **`law_initLaw`** (the law at time `t` from the initial law is the push-forward of
  `P ⊗ noise₂` along the hybrid trajectory at time `t`).
-/
import UncomputableNoiseDiagram.Memory.Init

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

namespace UND.Memory

open UND.Rule UND.Sensors
open FNE (Plane box)

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData B τ} (s : ℕ)

/-! ## Measurability and covariance of the initialization -/

/-- **The initialization is measurable** in (chart parameter, negative-time noise). -/
theorem measurable_X0 {Θ : Type*} [MeasurableSpace Θ] (cSf : Θ → Plane → ChartSym CD.toWangRel)
    (hcS : ∀ u σ, MeasurableSet {θ | cSf θ u = σ}) :
    Measurable (fun p : Θ × (ruleCA CD s).Noise => X0 s (cSf p.1) p.2) := by
  classical
  have hog : ∀ u, Measurable (fun p : Θ × (ruleCA CD s).Noise => ogOf (cSf p.1 u)) := by
    intro u
    refine measurable_to_countable' fun bo => ?_
    have e : (fun p : Θ × (ruleCA CD s).Noise => ogOf (cSf p.1 u)) ⁻¹' {bo} =
        Prod.fst ⁻¹' (⋃ σ ∈ {σ : ChartSym CD.toWangRel | ogOf σ = bo}, {θ | cSf θ u = σ}) := by
      ext p
      simp
    rw [e]
    exact measurable_fst (MeasurableSet.biUnion (Set.to_countable _) fun σ _ => hcS u σ)
  have hseq : ∀ (j : Fin B) (w : ISite),
      Measurable (fun p : Θ × (ruleCA CD s).Noise => seqOf (cSf p.1) (pastN s p.2) j w) := by
    intro j w
    refine measurable_pi_iff.2 fun m => ?_
    exact Measurable.prodMk ((measurable_pi_apply _).comp measurable_snd) (hog _)
  have hfield : ∀ (j : Fin B) (w : ISite) (h : Helper), MeasurableSet
      {p : Θ × (ruleCA CD s).Noise | initField' (cSf p.1) (pastN s p.2) j w = h} :=
    fun j w h => hseq j w (measurableSet_firstHit hitX (valX j) Ival.zero.repr h)
  refine measurable_pi_iff.2 fun w6 => measurable_to_countable' fun v => ?_
  set F : Θ × (ruleCA CD s).Noise → PhysSym CD := fun p =>
    (cSf p.1 (siteEquiv w6).1, cSf p.1 (siteEquiv w6).1,
      fun j => initField' (cSf p.1) (pastN s p.2) j (siteEquiv w6)) with hF
  have e1 : (fun p : Θ × (ruleCA CD s).Noise => X0 s (cSf p.1) p.2 w6) ⁻¹' {v} =
      F ⁻¹' {(Fintype.equivFin (PhysSym CD)).symm v} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff]
    exact (Equiv.eq_symm_apply (Fintype.equivFin (PhysSym CD))).symm
  set σ := (Fintype.equivFin (PhysSym CD)).symm v
  have e2 : F ⁻¹' {σ} =
      ({p | cSf p.1 (siteEquiv w6).1 = σ.1} ∩ {p | cSf p.1 (siteEquiv w6).1 = σ.2.1}) ∩
        ⋂ j : Fin B, {p | initField' (cSf p.1) (pastN s p.2) j (siteEquiv w6) = σ.2.2 j} := by
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, hF, Set.mem_inter_iff, Set.mem_iInter,
      Set.mem_ofPred_eq, Prod.ext_iff, funext_iff, and_assoc]
  rw [e1, e2]
  refine MeasurableSet.inter (MeasurableSet.inter (measurable_fst (hcS _ _))
    (measurable_fst (hcS _ _))) (MeasurableSet.iInter fun j => hfield _ _ _)

/-- **The initialization is translation covariant.** -/
theorem X0_shift (cS cS' : Plane → ChartSym CD.toWangRel) (a6 : UND.Site 6)
    (h : ∀ u, cS (u + (siteEquiv a6).1) = cS' u) (a : (ruleCA CD s).Noise) :
    (ruleCA CD s).shift a6 (X0 s cS a) = X0 s cS' ((ruleCA CD s).shiftNoise a6 a) := by
  funext w6
  show Fintype.equivFin (PhysSym CD) _ = Fintype.equivFin (PhysSym CD) _
  congr 1
  rw [map_add]
  refine Prod.ext ?_ (Prod.ext ?_ (funext fun j => ?_))
  · show cS (siteEquiv w6 + siteEquiv a6).1 = cS' (siteEquiv w6).1
    rw [Prod.fst_add, h]
  · show cS (siteEquiv w6 + siteEquiv a6).1 = cS' (siteEquiv w6).1
    rw [Prod.fst_add, h]
  · show initField' cS (pastN s a) j (siteEquiv w6 + siteEquiv a6) =
      initField' cS' (pastN s ((ruleCA CD s).shiftNoise a6 a)) j (siteEquiv w6)
    unfold initField'
    congr 1
    funext m
    simp only [seqOf, chainSite_add]
    refine Prod.ext ?_ ?_
    · show a (m, siteEquiv.symm (chainSite (siteEquiv w6) m + siteEquiv a6)) =
        a (m, siteEquiv.symm (chainSite (siteEquiv w6) m) + a6)
      rw [map_add, AddEquiv.symm_apply_apply]
    · show ogOf (cS (chainSite (siteEquiv w6) m + siteEquiv a6 - jy j).1) =
        ogOf (cS' (chainSite (siteEquiv w6) m - jy j).1)
      rw [← h, add_sub_right_comm, Prod.fst_add]

/-! ## The initial law -/

/-- **The initial law of Section 7**: the chart parameter with law `P`, the negative-time noise
independent, pushed along the initialization `X0`. -/
def initLaw {Θ : Type*} [MeasurableSpace Θ] (P : Measure Θ)
    (cSf : Θ → Plane → ChartSym CD.toWangRel) (ε : ℝ) : Measure (ruleCA CD s).Config :=
  (P.prod ((ruleCA CD s).noiseLaw ε)).map (fun p => X0 s (cSf p.1) p.2)

theorem isProbabilityMeasure_initLaw {Θ : Type*} [MeasurableSpace Θ] (P : Measure Θ)
    [IsProbabilityMeasure P] (cSf : Θ → Plane → ChartSym CD.toWangRel)
    (hcS : ∀ u σ, MeasurableSet {θ | cSf θ u = σ}) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsProbabilityMeasure (initLaw s P cSf ε) := by
  have := (ruleCA CD s).isProbabilityMeasure_noiseLaw h0 h1
  exact (Measure.isProbabilityMeasure_map_iff (measurable_X0 s cSf hcS).aemeasurable).2
    inferInstance

/-- **The initial law is translation invariant** when every translation is matched by a
`P`-preserving map of the chart parameter (almost surely). -/
theorem initLaw_TI {Θ : Type*} [MeasurableSpace Θ] (P : Measure Θ) [IsProbabilityMeasure P]
    (cSf : Θ → Plane → ChartSym CD.toWangRel) (hcS : ∀ u σ, MeasurableSet {θ | cSf θ u = σ})
    {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (hcov : ∀ a6 : UND.Site 6, ∃ g : Θ → Θ, Measurable g ∧ P.map g = P ∧
      ∀ᵐ θ ∂P, ∀ u, cSf θ (u + (siteEquiv a6).1) = cSf (g θ) u) :
    (ruleCA CD s).IsTranslationInvariant (initLaw s P cSf ε) := by
  intro a6
  obtain ⟨g, hg, hPg, hae⟩ := hcov a6
  have hν := (ruleCA CD s).isProbabilityMeasure_noiseLaw h0 h1
  have hX := measurable_X0 s cSf hcS
  unfold initLaw
  rw [Measure.map_map ((ruleCA CD s).measurable_shift a6) hX]
  have hfst : (P.prod ((ruleCA CD s).noiseLaw ε)).map Prod.fst = P := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  have hae' : ∀ᵐ p ∂(P.prod ((ruleCA CD s).noiseLaw ε)),
      ∀ u, cSf p.1 (u + (siteEquiv a6).1) = cSf (g p.1) u :=
    ae_of_ae_map measurable_fst.aemeasurable (hfst.symm ▸ hae)
  have hcongr : ((ruleCA CD s).shift a6 ∘ fun p : Θ × (ruleCA CD s).Noise => X0 s (cSf p.1) p.2)
      =ᵐ[P.prod ((ruleCA CD s).noiseLaw ε)]
      ((fun p : Θ × (ruleCA CD s).Noise => X0 s (cSf p.1) p.2) ∘
        Prod.map g ((ruleCA CD s).shiftNoise a6)) := by
    filter_upwards [hae'] with p hp
    exact X0_shift s _ _ a6 hp p.2
  rw [Measure.map_congr hcongr, ← Measure.map_map hX
    (hg.prodMap ((ruleCA CD s).measurable_shiftNoise a6)),
    ← Measure.map_prod_map _ _ hg ((ruleCA CD s).measurable_shiftNoise a6), hPg,
    (ruleCA CD s).noiseLaw_map_shiftNoise h0 h1]

/-! ## Gluing negative and positive times -/

/-- A negative-time noise (`n ↦` time `-n`) and a positive-time noise (`n ↦` time `n + 1`) make a
two-sided noise. -/
def glue (p : (ruleCA CD s).Noise × (ruleCA CD s).Noise) : (ruleCA CD s).Noise₂ := fun i =>
  if i.1 ≤ 0 then p.1 ((-i.1).toNat, i.2) else p.2 ((i.1 - 1).toNat, i.2)

theorem measurable_glue : Measurable (glue (CD := CD) s) := by
  refine measurable_pi_iff.2 fun i => ?_
  by_cases h : i.1 ≤ 0
  · simp only [glue, h, ↓reduceIte]
    exact (measurable_pi_apply _).comp measurable_fst
  · simp only [glue, h, ↓reduceIte]
    exact (measurable_pi_apply _).comp measurable_snd

theorem negPart_glue (p : (ruleCA CD s).Noise × (ruleCA CD s).Noise) :
    negPart s (glue s p) = p.1 := by
  funext q
  have h : -(q.1 : ℤ) ≤ 0 := by omega
  simp [negPart, glue, h]

theorem posPart_glue (p : (ruleCA CD s).Noise × (ruleCA CD s).Noise) :
    posPart s (glue s p) = p.2 := by
  funext q
  have h : ¬ ((q.1 : ℤ) + 1 ≤ 0) := by omega
  simp [posPart, glue, h]

theorem measurable_negPart : Measurable (negPart (CD := CD) s) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

theorem measurable_posPart : Measurable (posPart (CD := CD) s) :=
  measurable_pi_iff.2 fun _ => measurable_pi_apply _

/-- **Gluing preserves the noise law**: the negative-time and positive-time parts of the two-sided
noise are independent copies of the one-sided noise. -/
theorem glue_law {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    (((ruleCA CD s).noiseLaw ε).prod ((ruleCA CD s).noiseLaw ε)).map (glue s) =
      (ruleCA CD s).noiseLaw₂ ε := by
  classical
  have hm := (ruleCA CD s).isProbabilityMeasure_noiseSite h0 h1
  have hν := (ruleCA CD s).isProbabilityMeasure_noiseLaw h0 h1
  unfold CA.noiseLaw₂
  refine Measure.eq_infinitePi (hμ := fun _ => hm) _ fun S t ht => ?_
  have hmeas : MeasurableSet (Set.pi (S : Set (ℤ × UND.Site 6)) t) :=
    MeasurableSet.pi (Set.to_countable _) fun i _ => ht i
  rw [Measure.map_apply (measurable_glue s) hmeas]
  have eN : ∀ i : ℤ × UND.Site 6, i.1 ≤ 0 → ((-(((-i.1).toNat : ℕ) : ℤ)), i.2) = i :=
    fun i hi => Prod.ext (by simp only; omega) rfl
  have eP : ∀ i : ℤ × UND.Site 6, ¬ i.1 ≤ 0 → (((((i.1 - 1).toNat : ℕ) : ℤ) + 1), i.2) = i :=
    fun i hi => Prod.ext (by simp only; omega) rfl
  have hpre : glue s ⁻¹' (Set.pi (S : Set (ℤ × UND.Site 6)) t) =
      (Set.pi (((S.filter fun i => i.1 ≤ 0).image fun i => ((-i.1).toNat, i.2) :
          Finset (ℕ × UND.Site 6)) : Set (ℕ × UND.Site 6)) fun j => t (-(j.1 : ℤ), j.2)) ×ˢ
        (Set.pi (((S.filter fun i => ¬ i.1 ≤ 0).image fun i => ((i.1 - 1).toNat, i.2) :
          Finset (ℕ × UND.Site 6)) : Set (ℕ × UND.Site 6)) fun j => t ((j.1 : ℤ) + 1, j.2)) := by
    ext p
    constructor
    · intro h
      refine ⟨fun j hj => ?_, fun j hj => ?_⟩
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hj)
        obtain ⟨hiS, hi0⟩ := Finset.mem_filter.1 hi
        have := h i hiS
        simp only [glue, hi0, ↓reduceIte] at this
        show p.1 ((-i.1).toNat, i.2) ∈ t (-(((-i.1).toNat : ℕ) : ℤ), i.2)
        rw [eN i hi0]
        exact this
      · obtain ⟨i, hi, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hj)
        obtain ⟨hiS, hi0⟩ := Finset.mem_filter.1 hi
        have := h i hiS
        simp only [glue, hi0, ↓reduceIte] at this
        show p.2 ((i.1 - 1).toNat, i.2) ∈ t ((((i.1 - 1).toNat : ℕ) : ℤ) + 1, i.2)
        rw [eP i hi0]
        exact this
    · rintro ⟨hN, hP⟩ i hi
      by_cases hi0 : i.1 ≤ 0
      · have := hN ((-i.1).toNat, i.2) (Finset.mem_coe.2 (Finset.mem_image.2
          ⟨i, Finset.mem_filter.2 ⟨hi, hi0⟩, rfl⟩))
        have e := eN i hi0
        simp only at this
        rw [e] at this
        show glue s p i ∈ t i
        simp only [glue, hi0, ↓reduceIte]
        exact this
      · have := hP ((i.1 - 1).toNat, i.2) (Finset.mem_coe.2 (Finset.mem_image.2
          ⟨i, Finset.mem_filter.2 ⟨hi, hi0⟩, rfl⟩))
        have e := eP i hi0
        simp only at this
        rw [e] at this
        show glue s p i ∈ t i
        simp only [glue, hi0, ↓reduceIte]
        exact this
  rw [hpre, Measure.prod_prod]
  unfold CA.noiseLaw
  rw [Measure.infinitePi_pi _ (fun j _ => ht _), Measure.infinitePi_pi _ (fun j _ => ht _)]
  have hinjN : Set.InjOn (fun i : ℤ × UND.Site 6 => ((-i.1).toNat, i.2))
      ((S.filter fun i => i.1 ≤ 0 : Finset (ℤ × UND.Site 6)) : Set (ℤ × UND.Site 6)) := by
    intro i hi i' hi' h
    have h1' := (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
    have h2' := (Finset.mem_filter.1 (Finset.mem_coe.1 hi')).2
    obtain ⟨ha, hb⟩ := Prod.mk.inj h
    exact Prod.ext (by omega) hb
  have hinjP : Set.InjOn (fun i : ℤ × UND.Site 6 => ((i.1 - 1).toNat, i.2))
      ((S.filter fun i => ¬ i.1 ≤ 0 : Finset (ℤ × UND.Site 6)) : Set (ℤ × UND.Site 6)) := by
    intro i hi i' hi' h
    have h1' := (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
    have h2' := (Finset.mem_filter.1 (Finset.mem_coe.1 hi')).2
    obtain ⟨ha, hb⟩ := Prod.mk.inj h
    exact Prod.ext (by omega) hb
  rw [Finset.prod_image hinjN, Finset.prod_image hinjP,
    ← Finset.prod_filter_mul_prod_filter_not S (fun i => i.1 ≤ 0)]
  congr 1
  · refine Finset.prod_congr rfl fun i hi => ?_
    simp only
    rw [eN i (Finset.mem_filter.1 hi).2]
  · refine Finset.prod_congr rfl fun i hi => ?_
    simp only
    rw [eP i (Finset.mem_filter.1 hi).2]

/-! ## The evolution of the initial law -/

theorem encode_hyb (cS : Plane → ChartSym CD.toWangRel) (ω : PNoise CD) (t : ℕ) :
    encodeConfig s (hyb s cS ω t) = (ruleCA CD s).run (X0 s cS (negPart s ω)) (posPart s ω) t := by
  rw [hyb_nat, encode_decode]

/-- **The law at time `t` from the initial law** is the push-forward of
`P ⊗ (two-sided noise)` along the automaton run from the initialization (the hybrid trajectory at
time `t`, `encode_hyb`). -/
theorem law_initLaw {Θ : Type*} [MeasurableSpace Θ] (P : Measure Θ) [IsProbabilityMeasure P]
    (cSf : Θ → Plane → ChartSym CD.toWangRel) (hcS : ∀ u σ, MeasurableSet {θ | cSf θ u = σ})
    {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (t : ℕ) :
    (ruleCA CD s).law ε (initLaw s P cSf ε) t =
      (P.prod ((ruleCA CD s).noiseLaw₂ ε)).map (fun p : Θ × (ruleCA CD s).Noise₂ =>
        (ruleCA CD s).run (X0 s (cSf p.1) (negPart s p.2)) (posPart s p.2) t) := by
  have hν := (ruleCA CD s).isProbabilityMeasure_noiseLaw h0 h1
  have hX := measurable_X0 s cSf hcS
  have hR := (ruleCA CD s).measurable_run t
  have hHm : Measurable (fun p : Θ × (ruleCA CD s).Noise₂ =>
      (ruleCA CD s).run (X0 s (cSf p.1) (negPart s p.2)) (posPart s p.2) t) :=
    hR.comp (Measurable.prodMk (hX.comp (measurable_fst.prodMk
      ((measurable_negPart s).comp measurable_snd))) ((measurable_posPart s).comp measurable_snd))
  have hKm : Measurable (fun q : (Θ × (ruleCA CD s).Noise) × (ruleCA CD s).Noise =>
      ((q.1.1, glue s (q.1.2, q.2)) : Θ × (ruleCA CD s).Noise₂)) :=
    measurable_fst.fst.prodMk ((measurable_glue s).comp (measurable_fst.snd.prodMk measurable_snd))
  have hKlaw : ((P.prod ((ruleCA CD s).noiseLaw ε)).prod ((ruleCA CD s).noiseLaw ε)).map
      (fun q : (Θ × (ruleCA CD s).Noise) × (ruleCA CD s).Noise =>
        ((q.1.1, glue s (q.1.2, q.2)) : Θ × (ruleCA CD s).Noise₂)) =
      P.prod ((ruleCA CD s).noiseLaw₂ ε) := by
    have e : (fun q : (Θ × (ruleCA CD s).Noise) × (ruleCA CD s).Noise =>
        ((q.1.1, glue s (q.1.2, q.2)) : Θ × (ruleCA CD s).Noise₂)) =
        Prod.map id (glue s) ∘ MeasurableEquiv.prodAssoc := by
      funext q
      rfl
    rw [e, ← Measure.map_map (measurable_id.prodMap (measurable_glue s))
      MeasurableEquiv.prodAssoc.measurable,
      (measurePreserving_prodAssoc P ((ruleCA CD s).noiseLaw ε) ((ruleCA CD s).noiseLaw ε)).map_eq,
      ← Measure.map_prod_map _ _ measurable_id (measurable_glue s), Measure.map_id,
      glue_law s h0 h1]
  have hcomp : (fun q : (ruleCA CD s).Config × (ruleCA CD s).Noise =>
      (ruleCA CD s).run q.1 q.2 t) ∘ Prod.map (fun p : Θ × (ruleCA CD s).Noise =>
        X0 s (cSf p.1) p.2) id =
      (fun p : Θ × (ruleCA CD s).Noise₂ =>
        (ruleCA CD s).run (X0 s (cSf p.1) (negPart s p.2)) (posPart s p.2) t) ∘
      (fun q : (Θ × (ruleCA CD s).Noise) × (ruleCA CD s).Noise =>
        ((q.1.1, glue s (q.1.2, q.2)) : Θ × (ruleCA CD s).Noise₂)) := by
    funext q
    simp only [Function.comp, Prod.map, id, negPart_glue, posPart_glue]
  have hprod : ((P.prod ((ruleCA CD s).noiseLaw ε)).map
      (fun p : Θ × (ruleCA CD s).Noise => X0 s (cSf p.1) p.2)).prod ((ruleCA CD s).noiseLaw ε) =
      ((P.prod ((ruleCA CD s).noiseLaw ε)).prod ((ruleCA CD s).noiseLaw ε)).map
        (Prod.map (fun p : Θ × (ruleCA CD s).Noise => X0 s (cSf p.1) p.2) id) := by
    rw [← Measure.map_prod_map _ _ hX measurable_id, Measure.map_id]
  unfold CA.law initLaw
  rw [hprod, Measure.map_map hR (hX.prodMap measurable_id), hcomp, ← Measure.map_map hHm hKm,
    hKlaw]

end UND.Memory
