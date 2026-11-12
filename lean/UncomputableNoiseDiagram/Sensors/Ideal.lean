/-
# Section 6: the ideal experiments and the laws (14), (15) (N1, the probabilistic part)

Node N1 of `BLUEPRINT.md` (Part A.6), NEW (Mathlib: `ProbabilityTheory.iIndepFun_infinitePi`,
`iIndepFun.indepFun_finset`, `IndepFun.measure_inter_preimage_eq_mul`,
`Measure.infinitePi_map_eval`).

Paper (Section 6): "Fix a legal reference chart and drive ideal interval fields by its exact
instructions. A true origin resets to zero; other sites copy. The replacement mark is uniform on
`ℋ` because (2) is a product, even though the fields at a physical site share their flag. The upper
scalar mark is zero for LOW and one for UNKNOWN or HIGH; the lower scalar mark is one for HIGH and
zero otherwise. … On a finite ruler of depth `d`, the provisional end reads exactly `ℓ_d` update
atoms … Thus the ideal upper success probability is (14) `p̄_d = .99[1 - (1-ε)^{ℓ_d}]`. For a recent
window of `W` updates a lane bit is one exactly when its most recent replacement mark is a HIGH
alias; it is zero for LOW, UNKNOWN, or no replacement. Its probability is (15)
`p_W = .98[1 - (1-ε)^W]`."

Formalization (the probability of one ideal lane experiment; which atoms a ride reads is chart
geometry, Lemma 6.1):
* **`infinitePi_inter_eq_mul`**: under a product measure, events determined by disjoint finite sets
  of coordinates are independent (`DetBy`, `extend`);
* `RideEv g L`: along distinct atoms `L` (most recent first), the most recent replacement exists
  and its mark satisfies `g` (the ideal field copies along the ride and is reset at the origin, so
  the end reads the most recent replacement mark, or the reset value `{0}`);
  `measurableSet_rideEv`, `detBy_rideEv`;
* **`rideEv_real`**: `P(RideEv g L) = ρ(1 - (1-ε)^{|L|})` when the mark law gives `g` probability
  `ρ`;
* for the automaton's noise: `upMark j` (field `j` of the replacement mark is not LOW) and `loMark j`
  (HIGH) have probabilities `99/100` and `98/100` (`uniformLaw_upMark`, `uniformLaw_loMark`, from
  `uniformLaw_field`); **`upper_law`** (14) and **`lower_law`** (15).
-/
import UncomputableNoiseDiagram.Sensors.Tails
import UncomputableNoiseDiagram.Rule.Noise

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace UND.Sensors

/-! ## Independence of disjoint coordinate sets -/

section Indep

variable {I α : Type*} [MeasurableSpace α] [Nonempty α]

/-- An event determined by the coordinates in `S`. -/
def DetBy (S : Finset I) (A : Set (I → α)) : Prop :=
  ∀ ω ω', (∀ i ∈ S, ω i = ω' i) → (ω ∈ A ↔ ω' ∈ A)

open Classical in
/-- A partial configuration on `S`, extended by a fixed filler. -/
def extend (S : Finset I) (x : S → α) : I → α :=
  fun i => if h : i ∈ S then x ⟨i, h⟩ else Classical.arbitrary α

theorem measurable_extend (S : Finset I) : Measurable (extend (α := α) S) := by
  classical
  refine measurable_pi_iff.mpr fun i => ?_
  by_cases h : i ∈ S
  · have e : (fun x : S → α => extend S x i) = fun x => x ⟨i, h⟩ := by
      funext x; simp [extend, h]
    rw [e]
    exact measurable_pi_apply _
  · have e : (fun x : S → α => extend S x i) = fun _ => Classical.arbitrary α := by
      funext x; simp [extend, h]
    rw [e]
    exact measurable_const

theorem extend_restrict (S : Finset I) (ω : I → α) :
    ∀ i ∈ S, extend S (fun i : S => ω i) i = ω i := by
  intro i hi
  simp [extend, hi]

theorem preimage_of_detBy {S : Finset I} {A : Set (I → α)} (hA : DetBy S A) :
    A = (fun ω (i : S) => ω i) ⁻¹' (extend S ⁻¹' A) := by
  ext ω
  exact hA ω (extend S fun i : S => ω i) (fun i hi => (extend_restrict S ω i hi).symm)

/-- **Independence of disjoint coordinate sets**: under a product measure, events determined by
disjoint finite coordinate sets are independent. -/
theorem infinitePi_inter_eq_mul {P : I → Measure α} [∀ i, IsProbabilityMeasure (P i)]
    {S T : Finset I} (hST : Disjoint S T) {A B : Set (I → α)} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAS : DetBy S A) (hBT : DetBy T B) :
    Measure.infinitePi P (A ∩ B) = Measure.infinitePi P A * Measure.infinitePi P B := by
  have hI : iIndepFun (fun i (ω : I → α) => ω i) (Measure.infinitePi P) :=
    iIndepFun_infinitePi (X := fun _ x => x) (fun _ => measurable_id)
  have hST' := hI.indepFun_finset S T hST (fun i => measurable_pi_apply i)
  have h := hST'.measure_inter_preimage_eq_mul _ _ ((measurable_extend S) hA)
    ((measurable_extend T) hB)
  rw [← preimage_of_detBy hAS, ← preimage_of_detBy hBT] at h
  exact h

end Indep

/-! ## The ride experiment -/

section Ride

variable {I β : Type*} [DecidableEq I] [MeasurableSpace β] [Nonempty β]

/-- **The ideal lane experiment** along distinct atoms `L` (most recent first): the most recent
replacement exists and its mark satisfies `g`. -/
def RideEv (g : β → Bool) : List I → Set (I → Bool × β)
  | [] => ∅
  | a :: L => {ω | (ω a).1 = true ∧ g (ω a).2 = true} ∪ ({ω | (ω a).1 = false} ∩ RideEv g L)

theorem measurableSet_coord (a : I) {s : Set (Bool × β)} (hs : MeasurableSet s) :
    MeasurableSet {ω : I → Bool × β | ω a ∈ s} :=
  (measurable_pi_apply (X := fun _ : I => Bool × β) a) hs

theorem set_mark (a : I) (g : β → Bool) :
    {ω : I → Bool × β | (ω a).1 = true ∧ g (ω a).2 = true} =
      {ω | ω a ∈ ({true} : Set Bool) ×ˢ {b : β | g b = true}} := by
  ext ω; simp

theorem set_noflag (a : I) :
    {ω : I → Bool × β | (ω a).1 = false} =
      {ω | ω a ∈ ({false} : Set Bool) ×ˢ (Set.univ : Set β)} := by
  ext ω; simp

theorem measurableSet_rideEv (g : β → Bool) (hg : MeasurableSet {b : β | g b = true}) :
    ∀ L : List I, MeasurableSet (RideEv g L)
  | [] => MeasurableSet.empty
  | a :: L => by
    refine MeasurableSet.union ?_ (MeasurableSet.inter ?_ (measurableSet_rideEv g hg L))
    · rw [set_mark]
      exact measurableSet_coord a ((measurableSet_singleton true).prod hg)
    · rw [set_noflag]
      exact measurableSet_coord a ((measurableSet_singleton false).prod MeasurableSet.univ)

theorem detBy_rideEv (g : β → Bool) : ∀ L : List I, DetBy L.toFinset (RideEv g L)
  | [] => fun _ _ _ => Iff.rfl
  | a :: L => by
    intro ω ω' h
    have ha : ω a = ω' a := h a (by simp)
    have hL := detBy_rideEv g L ω ω' (fun i hi => h i (by simp at hi ⊢; exact Or.inr hi))
    show (ω ∈ {ω | (ω a).1 = true ∧ g (ω a).2 = true} ∪
        ({ω | (ω a).1 = false} ∩ RideEv g L)) ↔
      (ω' ∈ {ω | (ω a).1 = true ∧ g (ω a).2 = true} ∪ ({ω | (ω a).1 = false} ∩ RideEv g L))
    simp only [Set.mem_union, Set.mem_inter_iff, Set.mem_ofPred_eq, ha, hL]

/-- The law of one coordinate event under the product of the noise laws. -/
theorem infinitePi_coord {ν : Measure (Bool × β)} [IsProbabilityMeasure ν] (a : I)
    {s : Set (Bool × β)} (hs : MeasurableSet s) :
    Measure.infinitePi (fun _ : I => ν) {ω | ω a ∈ s} = ν s := by
  have h := Measure.infinitePi_map_eval (fun _ : I => ν) a
  calc Measure.infinitePi (fun _ : I => ν) {ω | ω a ∈ s} =
        (Measure.infinitePi (fun _ : I => ν)).map (fun x => x a) s :=
        (Measure.map_apply (measurable_pi_apply (X := fun _ : I => Bool × β) a) hs).symm
    _ = ν s := by rw [h]

/-- **The ride law**: if the replacement mark satisfies `g` with probability `ρ`, the ideal
experiment along `n` distinct atoms succeeds with probability `ρ(1 - (1 - ε)^n)`. -/
theorem rideEv_real {ε ρ : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) {ν : Measure β} [hν : IsProbabilityMeasure ν]
    (g : β → Bool) (hgm : MeasurableSet {b : β | g b = true}) (hg : ν.real {b | g b = true} = ρ) :
    ∀ L : List I, L.Nodup →
      (Measure.infinitePi (fun _ : I => (FNE.flagLaw ε).prod ν)).real (RideEv g L) =
        ρ * (1 - (1 - ε) ^ L.length)
  | [] => fun _ => by simp [RideEv]
  | a :: L => by
    intro hnd
    have := FNE.isProbabilityMeasure_flagLaw h0 h1
    obtain ⟨haL, hnd'⟩ := List.nodup_cons.mp hnd
    have ih := rideEv_real h0 h1 g hgm hg L hnd'
    set μ := Measure.infinitePi (fun _ : I => (FNE.flagLaw ε).prod ν) with hμ
    have hflag : ∀ b : Bool, FNE.flagLaw ε {b} = if b then ENNReal.ofReal ε
        else ENNReal.ofReal (1 - ε) := by
      intro b
      cases b <;> simp [FNE.flagLaw]
    have hA : μ {ω | (ω a).1 = true ∧ g (ω a).2 = true} =
        ENNReal.ofReal ε * ν {b | g b = true} := by
      rw [set_mark, hμ, infinitePi_coord a ((measurableSet_singleton true).prod hgm),
        Measure.prod_prod, hflag]
      rfl
    have hF : μ {ω | (ω a).1 = false} = ENNReal.ofReal (1 - ε) := by
      rw [set_noflag, hμ, infinitePi_coord a ((measurableSet_singleton false).prod
        MeasurableSet.univ), Measure.prod_prod, measure_univ, mul_one, hflag]
      rfl
    have hdisj : Disjoint {ω : I → Bool × β | (ω a).1 = true ∧ g (ω a).2 = true}
        ({ω | (ω a).1 = false} ∩ RideEv g L) := by
      rw [Set.disjoint_left]
      rintro ω ⟨h1, -⟩ ⟨h2, -⟩
      have h2' : (ω a).1 = false := h2
      rw [h1] at h2'
      exact Bool.noConfusion h2'
    have hdetA : DetBy {a} {ω : I → Bool × β | (ω a).1 = false} := by
      intro ω ω' h
      show (ω a).1 = false ↔ (ω' a).1 = false
      rw [h a (Finset.mem_singleton_self a)]
    have hST : Disjoint ({a} : Finset I) L.toFinset := by
      rw [Finset.disjoint_singleton_left]
      simpa using haL
    have hmF : MeasurableSet {ω : I → Bool × β | (ω a).1 = false} := by
      rw [set_noflag]
      exact measurableSet_coord a ((measurableSet_singleton false).prod MeasurableSet.univ)
    have hI := infinitePi_inter_eq_mul (P := fun _ : I => (FNE.flagLaw ε).prod ν) hST hmF
      (measurableSet_rideEv g hgm L) hdetA (detBy_rideEv g L)
    rw [← hμ] at hI
    show μ.real ({ω | (ω a).1 = true ∧ g (ω a).2 = true} ∪
      ({ω | (ω a).1 = false} ∩ RideEv g L)) = ρ * (1 - (1 - ε) ^ (L.length + 1))
    rw [measureReal_union hdisj (hmF.inter (measurableSet_rideEv g hgm L))]
    rw [measureReal_def, measureReal_def, hA, hI, ENNReal.toReal_mul, ENNReal.toReal_mul, hF,
      ENNReal.toReal_ofReal h0, ENNReal.toReal_ofReal (by linarith : (0 : ℝ) ≤ 1 - ε)]
    have e1 : (ν {b | g b = true}).toReal = ρ := hg
    have e2 : (μ (RideEv g L)).toReal = ρ * (1 - (1 - ε) ^ L.length) := ih
    rw [e1, e2]
    ring

end Ride

/-! ## The lane marks of the automaton's noise -/

section Lanes

open UND.Rule

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData B τ}

/-- The upper scalar mark of lane `j`: field `j` of the replacement mark is UNKNOWN or HIGH. -/
def upMark (j : Fin B) (z : Fin (Fintype.card (PhysSym CD))) : Bool :=
  decide (Helper.rep ((decodeSym z : PhysSym CD).2.2 j) ≠ Ival.zero)

/-- The lower scalar mark of lane `j`: field `j` of the replacement mark is a HIGH alias. -/
def loMark (j : Fin B) (z : Fin (Fintype.card (PhysSym CD))) : Bool :=
  decide (Helper.rep ((decodeSym z : PhysSym CD).2.2 j) = Ival.one)

/-- A mark determined by field `j` through a set `F` of helper letters has probability `|F|/100`. -/
theorem uniformLaw_fieldSet (G : (ISite → PhysSym CD) → (ISite → PhysSym CD)) (N : Finset ISite)
    (j : Fin B) (F : Finset Helper) :
    (caOf G N).uniformLaw {z | (decodeSym z : PhysSym CD).2.2 j ∈ F} = F.card * (100 : ℝ≥0∞)⁻¹ := by
  have e : {z : Fin (Fintype.card (PhysSym CD)) | (decodeSym z : PhysSym CD).2.2 j ∈ F} =
      ⋃ a ∈ F, decodeSym ⁻¹' {σ : PhysSym CD | σ.2.2 j = a} := by
    ext z
    simp
  have hd : (F : Set Helper).PairwiseDisjoint
      (fun a => (decodeSym ⁻¹' {σ : PhysSym CD | σ.2.2 j = a} : Set (caOf G N).Sym)) := by
    intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro z h1 h2
    exact hab (h1.symm.trans h2)
  have hm : ∀ a ∈ F,
      MeasurableSet (decodeSym ⁻¹' {σ : PhysSym CD | σ.2.2 j = a} : Set (caOf G N).Sym) :=
    fun a _ => (Set.toFinite _).measurableSet
  calc (caOf G N).uniformLaw {z | (decodeSym z : PhysSym CD).2.2 j ∈ F}
      = (caOf G N).uniformLaw (⋃ a ∈ F,
          (decodeSym ⁻¹' {σ : PhysSym CD | σ.2.2 j = a} : Set (caOf G N).Sym)) := congrArg _ e
    _ = ∑ a ∈ F, (caOf G N).uniformLaw
          (decodeSym ⁻¹' {σ : PhysSym CD | σ.2.2 j = a} : Set (caOf G N).Sym) :=
        measure_biUnion_finset hd hm
    _ = ∑ _a ∈ F, (100 : ℝ≥0∞)⁻¹ := Finset.sum_congr rfl (fun a _ => uniformLaw_field CD G N j a)
    _ = F.card * (100 : ℝ≥0∞)⁻¹ := by rw [Finset.sum_const, nsmul_eq_mul]

theorem uniformLaw_upMark (G : (ISite → PhysSym CD) → (ISite → PhysSym CD)) (N : Finset ISite)
    (j : Fin B) : ((caOf G N).uniformLaw).real {z | upMark (CD := CD) j z = true} = 99 / 100 := by
  have e : {z : Fin (Fintype.card (PhysSym CD)) | upMark (CD := CD) j z = true} =
      {z | (decodeSym z : PhysSym CD).2.2 j ∈
        Finset.univ.filter (fun a : Helper => Helper.rep a ≠ Ival.zero)} := by
    ext z
    simp [upMark]
  have hc : (Finset.univ.filter (fun a : Helper => Helper.rep a ≠ Ival.zero)).card = 99 := by
    decide
  have hmeas : (caOf G N).uniformLaw {z | upMark (CD := CD) j z = true} =
      ((Finset.univ.filter (fun a : Helper => Helper.rep a ≠ Ival.zero)).card : ℝ≥0∞) *
        (100 : ℝ≥0∞)⁻¹ :=
    (congrArg (caOf G N).uniformLaw e).trans (uniformLaw_fieldSet G N j _)
  rw [measureReal_def, hmeas, hc, ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num

theorem uniformLaw_loMark (G : (ISite → PhysSym CD) → (ISite → PhysSym CD)) (N : Finset ISite)
    (j : Fin B) : ((caOf G N).uniformLaw).real {z | loMark (CD := CD) j z = true} = 98 / 100 := by
  have e : {z : Fin (Fintype.card (PhysSym CD)) | loMark (CD := CD) j z = true} =
      {z | (decodeSym z : PhysSym CD).2.2 j ∈
        Finset.univ.filter (fun a : Helper => Helper.rep a = Ival.one)} := by
    ext z
    simp [loMark]
  have hmeas : (caOf G N).uniformLaw {z | loMark (CD := CD) j z = true} =
      ((Finset.univ.filter (fun a : Helper => Helper.rep a = Ival.one)).card : ℝ≥0∞) *
        (100 : ℝ≥0∞)⁻¹ :=
    (congrArg (caOf G N).uniformLaw e).trans (uniformLaw_fieldSet G N j _)
  rw [measureReal_def, hmeas, Helper.card_rep.2.2, ENNReal.toReal_mul, ENNReal.toReal_inv]
  norm_num

/-- **(14)**: the ideal upper experiment of lane `j` along `ℓ` distinct update atoms succeeds with
probability `.99[1 - (1 - ε)^ℓ]`. -/
theorem upper_law (G : (ISite → PhysSym CD) → (ISite → PhysSym CD)) (N : Finset ISite)
    (j : Fin B) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (L : List (ℤ × UND.Site 6)) (hL : L.Nodup) :
    ((caOf G N).noiseLaw₂ ε).real (RideEv (upMark (CD := CD) j) L) =
      99 / 100 * (1 - (1 - ε) ^ L.length) :=
  haveI : Nonempty (caOf G N).Sym := ⟨⟨0, (caOf G N).numSymbols_pos⟩⟩
  rideEv_real (hν := UND.CA.isProbabilityMeasure_uniformLaw (caOf G N)) h0 h1 (upMark j) (Set.toFinite _).measurableSet (uniformLaw_upMark G N j) L hL

/-- **(15)**: the ideal lower experiment of lane `j` over a window of `W` distinct update atoms
gives a one with probability `.98[1 - (1 - ε)^W]`. -/
theorem lower_law (G : (ISite → PhysSym CD) → (ISite → PhysSym CD)) (N : Finset ISite)
    (j : Fin B) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (L : List (ℤ × UND.Site 6)) (hL : L.Nodup) :
    ((caOf G N).noiseLaw₂ ε).real (RideEv (loMark (CD := CD) j) L) =
      98 / 100 * (1 - (1 - ε) ^ L.length) :=
  haveI : Nonempty (caOf G N).Sym := ⟨⟨0, (caOf G N).numSymbols_pos⟩⟩
  rideEv_real (hν := UND.CA.isProbabilityMeasure_uniformLaw (caOf G N)) h0 h1 (loMark j) (Set.toFinite _).measurableSet (uniformLaw_loMark G N j) L hL

end Lanes

end UND.Sensors
