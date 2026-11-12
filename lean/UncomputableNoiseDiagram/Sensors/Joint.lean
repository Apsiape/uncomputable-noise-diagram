/-
# Section 6: Lemma 6.3 (joint source bound) (N4), with Lemma 6.2 per bin (N3)

Node N4 of `BLUEPRINT.md` (Part A.6), NEW (Mathlib: `Finset.sum_pow_mul_eq_add_pow`).

Paper (Section 6): "Partition each characteristic (16) into bins `i_bin W ≤ t < (i_bin + 1)W`.
Write `R(χ_ch, i_bin)` for the event that some raw flag occurs on that characteristic in the bin.
On a phase-zero base characteristic write `S(χ_ch, i_bin)` for some intrinsic finite-gate failure
in that bin, and put `S = ∅` on other rows."

**Lemma 6.3.** "For any `g` distinct labels, `P{R ∪ S at all g labels} ≤ γ^g`,
`γ = √C + η̂_B^{1/6}` (19)." Proof: "Raw bins use disjoint atoms and have probability at most
`εW ≤ C`. A statistical bin uses its `B` private lane characteristics and at most its own and
preceding bins. Distinct base characteristic labels have disjoint lane characteristics by
Lemma 6.1. On each characteristic bins in one residue class modulo three have disjoint source
supports. A largest class therefore bounds an intersection of `g_S` statistical events by
`η̂_B^{g_S/3}`. For `g_R` distinct raw events, Cauchy–Schwarz gives the mixed bound
`C^{g_R/2} η̂_B^{g_S/6}`, without assuming that raw and statistical events are independent. Sum
over the two source-type choices at each label to obtain (19)."

Lemma 6.2: "In any `W`-time bin on one base characteristic, the probability that some finite gate
has an intrinsic bad event is at most `η̂_B`. … At most `3·4^{r_off}` short ends occur in a bin,
since their spacing is `4^{d+1}` and `W < 4^a`. … At most two long ends occur in a bin."

Formalization:
* **`joint_bound`** (abstract Lemma 6.3): for raw events on pairwise disjoint finite coordinate
  sets with probability `≤ C`, and statistical events with probability `≤ η ≤ 1` whose coordinate
  sets are disjoint within each of three classes, `P(⋂_{l ∈ G} (R_l ∪ S_l)) ≤ (√C + η^{1/6})^{|G|}`
  (the selection expansion `biInter_union_subset`, the product over the raw selection, the largest
  class `exists_big_class`, `min ≤ √(xy)`, and `Finset.sum_pow_mul_eq_add_pow`);
* labels `Label = ((c, y, Q), i)`; `rawList`, **`RawEv`** (some flag among the `W` outputs of the
  bin on the characteristic), `rawEv_le` (`≤ εW`);
* `GateBad` (short below the critical depth `a`, long from `a` on), **`StatEv`** (some finite
  phase-zero gate ending in the bin has its intrinsic bad event), `statSupp` (the `B` lane
  characteristics in this and the preceding bin; empty off phase-zero rows), `detBy_statEv`,
  `statSupp_disjoint` (Lemma 6.1's block partition and the residue classes mod 3);
* `Regime` (the parameter facts of (17), (18) used here), `card_ends_le` (ends of depth `d` in a
  bin), **`statEv_le`** (Lemma 6.2, the bin bound `≤ η̂_B`);
* **`joint_source_bound`** (Lemma 6.3 for the automaton's noise).
-/
import UncomputableNoiseDiagram.Sensors.Gate

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace UND.Sensors

/-! ## The abstract joint bound -/

section Abstract

theorem biInter_union_subset {Ω L : Type*} [DecidableEq L] (G : Finset L) (R S : L → Set Ω) :
    (⋂ l ∈ G, (R l ∪ S l)) ⊆ ⋃ A ∈ G.powerset, ((⋂ l ∈ A, R l) ∩ ⋂ l ∈ G \ A, S l) := by
  classical
  intro ω hω
  simp only [Set.mem_iInter, Set.mem_union] at hω
  simp only [Set.mem_iUnion, Set.mem_inter_iff, Set.mem_iInter, Finset.mem_powerset, exists_prop]
  refine ⟨G.filter (fun l => ω ∈ R l), Finset.filter_subset _ _,
    fun l hl => (Finset.mem_filter.1 hl).2, fun l hl => ?_⟩
  rw [Finset.mem_sdiff, Finset.mem_filter] at hl
  exact (hω l hl.1).resolve_left (fun h => hl.2 ⟨hl.1, h⟩)

/-- A largest of three classes holds at least a third of the elements. -/
theorem exists_big_class {L : Type*} (D : Finset L) (cls : L → ZMod 3) :
    ∃ c : ZMod 3, D.card ≤ 3 * (D.filter fun l => cls l = c).card := by
  classical
  by_contra h
  push Not at h
  have hsum := Finset.card_eq_sum_card_fiberwise (f := cls) (s := D) (t := Finset.univ)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _))
  have hlt : ∑ c ∈ (Finset.univ : Finset (ZMod 3)), 3 * (D.filter fun l => cls l = c).card <
      ∑ _c ∈ (Finset.univ : Finset (ZMod 3)), D.card :=
    Finset.sum_lt_sum_of_nonempty Finset.univ_nonempty fun c _ => h c
  rw [← Finset.mul_sum, ← hsum, Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul] at hlt
  omega

theorem min_le_sqrt_mul {x y m : ℝ} (hm : 0 ≤ m) (hx : m ≤ x) (hy : m ≤ y) : m ≤ √(x * y) :=
  (Real.le_sqrt hm (by nlinarith)).2 (by nlinarith)

variable {I α : Type*} [MeasurableSpace α] [Nonempty α] [DecidableEq I]
  {P : I → Measure α} [∀ i, IsProbabilityMeasure (P i)]

/-- The product of finitely many events on pairwise disjoint coordinate sets, in `ℝ`. -/
theorem real_biInter_eq_prod {L : Type*} [DecidableEq L] (a : L → Finset I)
    (A : L → Set (I → α)) (S : Finset L) (hd : ∀ k ∈ S, ∀ l ∈ S, k ≠ l → Disjoint (a k) (a l))
    (hA : ∀ k ∈ S, MeasurableSet (A k)) (hdet : ∀ k ∈ S, DetBy (a k) (A k)) :
    (Measure.infinitePi P).real (⋂ k ∈ S, A k) = ∏ k ∈ S, (Measure.infinitePi P).real (A k) := by
  rw [measureReal_def, infinitePi_biInter_eq_prod a A S hd hA hdet, ENNReal.toReal_prod]
  rfl

/-- **Lemma 6.3, abstract form.** Raw events `R_l` on pairwise disjoint finite coordinate sets with
probability at most `C`; statistical events `S_l` with probability at most `η ≤ 1` whose
coordinate sets are disjoint within each residue class `cls l ∈ ℤ/3`. Then for any finite set `G`
of labels, `P(⋂_{l ∈ G} (R_l ∪ S_l)) ≤ (√C + η^{1/6})^{|G|}`; no independence between raw and
statistical events is assumed. -/
theorem joint_bound {L : Type*} [DecidableEq L] (G : Finset L) (R S : L → Set (I → α))
    (aR aS : L → Finset I) (hRm : ∀ l, MeasurableSet (R l)) (hSm : ∀ l, MeasurableSet (S l))
    (hRd : ∀ l, DetBy (aR l) (R l)) (hSd : ∀ l, DetBy (aS l) (S l))
    (hRdisj : ∀ l ∈ G, ∀ l' ∈ G, l ≠ l' → Disjoint (aR l) (aR l'))
    (cls : L → ZMod 3)
    (hSdisj : ∀ l ∈ G, ∀ l' ∈ G, l ≠ l' → cls l = cls l' → Disjoint (aS l) (aS l'))
    {C η : ℝ} (hC : 0 ≤ C) (hη : 0 ≤ η) (hη1 : η ≤ 1)
    (hR : ∀ l ∈ G, (Measure.infinitePi P).real (R l) ≤ C)
    (hS : ∀ l ∈ G, (Measure.infinitePi P).real (S l) ≤ η) :
    (Measure.infinitePi P).real (⋂ l ∈ G, (R l ∪ S l)) ≤ (√C + η ^ ((1 : ℝ) / 6)) ^ G.card := by
  classical
  set μ := Measure.infinitePi P with hμ
  -- the raw part of a selection
  have hRA : ∀ A ⊆ G, μ.real (⋂ l ∈ A, R l) ≤ C ^ A.card := by
    intro A hA
    rw [real_biInter_eq_prod aR R A (fun k hk l hl => hRdisj k (hA hk) l (hA hl))
      (fun k _ => hRm k) (fun k _ => hRd k), ← Finset.prod_const]
    exact Finset.prod_le_prod₀ (fun _ _ => measureReal_nonneg) (fun l hl => hR l (hA hl))
  -- the statistical part of a selection: a largest residue class
  have hSD : ∀ D ⊆ G, μ.real (⋂ l ∈ D, S l) ≤ (η ^ ((1 : ℝ) / 3)) ^ D.card := by
    intro D hD
    obtain ⟨c, hc⟩ := exists_big_class D cls
    set Dc := D.filter fun l => cls l = c with hDc
    have hsub : (⋂ l ∈ D, S l) ⊆ ⋂ l ∈ Dc, S l := by
      intro ω hω
      simp only [Set.mem_iInter] at hω ⊢
      exact fun l hl => hω l (Finset.mem_filter.1 hl).1
    have hDcG : ∀ l ∈ Dc, l ∈ G := fun l hl => hD (Finset.mem_filter.1 hl).1
    have h1 : μ.real (⋂ l ∈ Dc, S l) ≤ η ^ Dc.card := by
      rw [real_biInter_eq_prod aS S Dc (fun k hk l hl hkl => hSdisj k (hDcG k hk) l (hDcG l hl) hkl
        (((Finset.mem_filter.1 hk).2).trans ((Finset.mem_filter.1 hl).2).symm))
        (fun k _ => hSm k) (fun k _ => hSd k), ← Finset.prod_const]
      exact Finset.prod_le_prod₀ (fun _ _ => measureReal_nonneg) (fun l hl => hS l (hDcG l hl))
    have h2 : η ^ Dc.card ≤ (η ^ ((1 : ℝ) / 3)) ^ D.card := by
      rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hη]
      refine Real.rpow_le_rpow_of_exponent_ge' hη hη1 (by positivity) ?_
      have : (D.card : ℝ) ≤ 3 * Dc.card := by exact_mod_cast hc
      linarith
    exact (measureReal_mono hsub (measure_ne_top _ _)).trans (h1.trans h2)
  -- one selection
  have hsel : ∀ A ∈ G.powerset, μ.real ((⋂ l ∈ A, R l) ∩ ⋂ l ∈ G \ A, S l) ≤
      √C ^ A.card * (η ^ ((1 : ℝ) / 6)) ^ (G.card - A.card) := by
    intro A hA
    rw [Finset.mem_powerset] at hA
    have hx := hRA A hA
    have hy := hSD (G \ A) Finset.sdiff_subset
    rw [Finset.card_sdiff_of_subset hA] at hy
    have hm1 : μ.real ((⋂ l ∈ A, R l) ∩ ⋂ l ∈ G \ A, S l) ≤ μ.real (⋂ l ∈ A, R l) :=
      measureReal_mono Set.inter_subset_left (measure_ne_top _ _)
    have hm2 : μ.real ((⋂ l ∈ A, R l) ∩ ⋂ l ∈ G \ A, S l) ≤ μ.real (⋂ l ∈ G \ A, S l) :=
      measureReal_mono Set.inter_subset_right (measure_ne_top _ _)
    have hcs := min_le_sqrt_mul measureReal_nonneg (hm1.trans hx) (hm2.trans hy)
    refine hcs.trans (le_of_eq ?_)
    have e1 : (η ^ ((1 : ℝ) / 3)) = (η ^ ((1 : ℝ) / 6)) ^ 2 := by
      rw [← Real.rpow_natCast, ← Real.rpow_mul hη]; norm_num
    rw [e1, ← pow_mul, Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity)]
    have e2 : C = √C ^ 2 := (Real.sq_sqrt hC).symm
    conv_lhs => rw [e2]
    ring
  calc μ.real (⋂ l ∈ G, (R l ∪ S l))
      ≤ μ.real (⋃ A ∈ G.powerset, ((⋂ l ∈ A, R l) ∩ ⋂ l ∈ G \ A, S l)) :=
        measureReal_mono (biInter_union_subset G R S) (measure_ne_top _ _)
    _ ≤ ∑ A ∈ G.powerset, μ.real ((⋂ l ∈ A, R l) ∩ ⋂ l ∈ G \ A, S l) :=
        measureReal_biUnion_finset_le _ _
    _ ≤ ∑ A ∈ G.powerset, √C ^ A.card * (η ^ ((1 : ℝ) / 6)) ^ (G.card - A.card) :=
        Finset.sum_le_sum hsel
    _ = (√C + η ^ ((1 : ℝ) / 6)) ^ G.card := Finset.sum_pow_mul_eq_add_pow _ _ _

end Abstract

/-! ## Raw and statistical bins -/

section Bins

open UND.Rule UPD.Scaffold UND.Chart

/-- Right endpoints of depth-`d` frames: `z = a_d + 3·4^d + 4^{d+1} m`. -/
theorem isRightEnd_iff (a : ℕ → ℤ) (d : ℕ) (z : ℤ) :
    IsRightEnd a d z ↔ (4 : ℤ) ^ (d + 1) ∣ z - a d - 3 * 4 ^ d := by
  constructor
  · rintro ⟨m, rfl⟩
    exact ⟨m, by simp only [frameHi]; ring⟩
  · rintro ⟨m, hm⟩
    exact ⟨m, by simp only [frameHi]; linear_combination hm⟩

instance (a : ℕ → ℤ) (d : ℕ) : DecidablePred (IsRightEnd a d) := fun z =>
  decidable_of_iff _ (isRightEnd_iff a d z).symm

/-- **Ends in a bin**: among `W ≤ 4^{d+1} R` consecutive coordinates at most `R` are depth-`d`
right endpoints. -/
theorem card_ends_le (a : ℕ → ℤ) (d : ℕ) (x0 : ℤ) {W R : ℕ} (hW : W ≤ 4 ^ (d + 1) * R) :
    ((Finset.range W).filter fun i : ℕ => IsRightEnd a d (x0 + i)).card ≤ R := by
  have hM : 0 < 4 ^ (d + 1) := by positivity
  calc ((Finset.range W).filter fun i : ℕ => IsRightEnd a d (x0 + i)).card
      ≤ (Finset.range R).card := by
        refine Finset.card_le_card_of_injOn (fun i => i / 4 ^ (d + 1)) ?_ ?_
        · intro i hi
          have hi' := (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).1
          rw [Finset.mem_range] at hi'
          rw [Finset.coe_range, Set.mem_Iio]
          exact Nat.div_lt_of_lt_mul (by linarith)
        · intro i hi i₂ hi₂ h
          have h1 := (Finset.mem_filter.1 (Finset.mem_coe.1 hi)).2
          have h2 := (Finset.mem_filter.1 (Finset.mem_coe.1 hi₂)).2
          have hdvd := UND.Sensors.rightEnd_dvd h1 h2
          have e1 := Nat.div_add_mod i (4 ^ (d + 1))
          have e2 := Nat.div_add_mod i₂ (4 ^ (d + 1))
          have hr1 := Nat.mod_lt i hM
          have hr2 := Nat.mod_lt i₂ hM
          have hq : i / 4 ^ (d + 1) = i₂ / 4 ^ (d + 1) := h
          have hlt : |(x0 + (i : ℤ)) - (x0 + i₂)| < 4 ^ (d + 1) := by
            rw [abs_lt]
            have e1' : (i : ℤ) = 4 ^ (d + 1) * ((i / 4 ^ (d + 1) : ℕ) : ℤ) +
                ((i % 4 ^ (d + 1) : ℕ) : ℤ) := by exact_mod_cast e1.symm
            have e2' : (i₂ : ℤ) = 4 ^ (d + 1) * ((i₂ / 4 ^ (d + 1) : ℕ) : ℤ) +
                ((i₂ % 4 ^ (d + 1) : ℕ) : ℤ) := by exact_mod_cast e2.symm
            have hr1' : ((i % 4 ^ (d + 1) : ℕ) : ℤ) < 4 ^ (d + 1) := by exact_mod_cast hr1
            have hr2' : ((i₂ % 4 ^ (d + 1) : ℕ) : ℤ) < 4 ^ (d + 1) := by exact_mod_cast hr2
            rw [hq] at e1'
            constructor <;> linarith [(Nat.cast_nonneg (i % 4 ^ (d + 1)) : (0 : ℤ) ≤ _),
              (Nat.cast_nonneg (i₂ % 4 ^ (d + 1)) : (0 : ℤ) ≤ _)]
          have := Int.eq_zero_of_abs_lt_dvd hdvd hlt
          exact_mod_cast (by linarith : (i : ℤ) = i₂)
    _ = R := Finset.card_range R

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData B τ}

/-- A source label `(χ_ch, i_bin)`: a base characteristic `(c, y, Q)` and a bin index. -/
abbrev Label := (ℤ × ℤ × (Fin 4 → ℤ)) × ℤ

/-- The atoms of the `W` outputs of the bin on the characteristic of a label. -/
def rawList (W : ℕ) (l : Label) : List (ℤ × UND.Site 6) :=
  (List.range W).map fun i : ℕ => laneAtom l.1.1 l.1.2.1 l.1.2.2 0 (l.2 * W + (i : ℤ))

/-- **`R(χ_ch, i_bin)`**: some raw flag occurs on the characteristic in the bin. -/
def RawEv (CD : ChartData B τ) (W : ℕ) (l : Label) : Set (PNoise CD) :=
  RideEv (fun _ : Fin (Fintype.card (PhysSym CD)) => true) (rawList W l)

theorem rawList_nodup (W : ℕ) (l : Label) : (rawList W l).Nodup := by
  refine List.Nodup.map (fun i i₂ h => ?_) List.nodup_range
  have := (laneAtom_inj h).1
  exact_mod_cast (by linarith : (i : ℤ) = i₂)

theorem rawList_length (W : ℕ) (l : Label) : (rawList W l).length = W := by
  simp [rawList]

/-- Raw bins of distinct labels use disjoint atoms. -/
theorem rawSupp_disjoint (W : ℕ) {l l₂ : Label} (hne : l ≠ l₂) :
    Disjoint (rawList W l).toFinset (rawList W l₂).toFinset := by
  rw [Finset.disjoint_left]
  intro p hp hp₂
  simp only [rawList, List.mem_toFinset, List.mem_map, List.mem_range] at hp hp₂
  obtain ⟨i, hi, rfl⟩ := hp
  obtain ⟨i₂, hi₂, h⟩ := hp₂
  obtain ⟨ht, hc, hy, hQ⟩ := laneAtom_inj h
  have hy₂ : l₂.1.2.1 = l.1.2.1 := by simpa using hy
  have hi1 : (i : ℤ) < W := by exact_mod_cast hi
  have hi2 : (i₂ : ℤ) < W := by exact_mod_cast hi₂
  have hbin : l₂.2 = l.2 := by
    by_contra hb
    rcases lt_or_gt_of_ne hb with hb | hb
    · have : l₂.2 + 1 ≤ l.2 := hb
      nlinarith [(Nat.cast_nonneg i : (0 : ℤ) ≤ i), (Nat.cast_nonneg i₂ : (0 : ℤ) ≤ i₂)]
    · have : l.2 + 1 ≤ l₂.2 := hb
      nlinarith [(Nat.cast_nonneg i : (0 : ℤ) ≤ i), (Nat.cast_nonneg i₂ : (0 : ℤ) ≤ i₂)]
  exact hne (Prod.ext (Prod.ext hc.symm (Prod.ext hy₂.symm hQ.symm)) hbin.symm)

/-- `P(R) = 1 - (1-ε)^W ≤ εW`. -/
theorem rawEv_le (G : (ISite → PhysSym CD) → (ISite → PhysSym CD)) (N : Finset ISite) {ε : ℝ}
    (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (W : ℕ) (l : Label) :
    (pLaw G N ε).real (RawEv CD W l) ≤ ε * W := by
  have : Nonempty (caOf G N).Sym := ⟨⟨0, (caOf G N).numSymbols_pos⟩⟩
  have hu := UND.CA.isProbabilityMeasure_uniformLaw (caOf G N)
  have hg : ((caOf G N).uniformLaw).real {b | (fun _ : (caOf G N).Sym => true) b = true} = 1 := by
    simp
  have h := rideEv_real (hν := hu) h0 h1 (fun _ : (caOf G N).Sym => true)
    (Set.toFinite _).measurableSet hg (rawList W l) (rawList_nodup W l)
  rw [rawList_length, one_mul] at h
  have hb := one_add_mul_le_pow (a := -ε) (by linarith) W
  rw [show (1 + -ε) = 1 - ε by ring] at hb
  calc (pLaw G N ε).real (RawEv CD W l)
      = 1 - (1 - ε) ^ W := by rw [← h]; rfl
    _ ≤ ε * W := by linarith

/-- The parameter facts of (17), (18) used by the sensors (Prop 9.2 supplies them on every window
with `W = ⌊C/ε⌋`, `a = n + n₀`, `s = ⌈3CB/4⌉`). -/
structure Regime (C ε : ℝ) (a W s B : ℕ) : Prop where
  C_pos : 0 < C
  C_le : C ≤ 1 / 100
  eps_nonneg : 0 ≤ ε
  eps_le : ε ≤ 1
  a_ge : 3 ≤ a
  eps_lt : ε < 21 * C / (10 * (UND.Windows.ell a : ℝ))
  epsW_ge : 99 / 100 * C ≤ ε * W
  epsW_le : ε * W ≤ C
  ell_lt : UND.Windows.ell (a - 1) < W
  W_le : 2 * W ≤ UND.Windows.ell a
  s_ge : 3 / 4 * C * B ≤ s
  s_le : (s : ℝ) ≤ 8 / 10 * C * B

theorem ell_mono {d d₂ : ℕ} (h : d ≤ d₂) : UND.Windows.ell d ≤ UND.Windows.ell d₂ := by
  unfold UND.Windows.ell
  have := Nat.pow_le_pow_right (by norm_num : 0 < 4) h
  omega

theorem Regime.ell_le {C ε : ℝ} {a W s B : ℕ} (hR : Regime C ε a W s B) {d : ℕ} (hd : d < a) :
    UND.Windows.ell d ≤ W :=
  (ell_mono (by omega)).trans hR.ell_lt.le

theorem Regime.W_le_four {C ε : ℝ} {a W s B : ℕ} (hR : Regime C ε a W s B) : W ≤ 4 ^ a := by
  have h := hR.W_le
  unfold UND.Windows.ell at h
  omega

/-- The intrinsic bad event of a finite phase-zero gate of depth `d` ending at `t` on `(c, y, Q)`:
short (`≥ s` upper successes along `ℓ_d` atoms) below the critical depth `a`, long (`< s` lower
successes along the recent `W` atoms) from `a` on. -/
def GateBad (CD : ChartData B τ) (s a W d : ℕ) (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ) :
    Set (PNoise CD) :=
  if d < a then ShortBad CD s c y Q t (UND.Windows.ell d) else LongBad CD s c y Q t W

/-- The number of atoms per lane read by `GateBad`. -/
def gateLen (a W d : ℕ) : ℕ := if d < a then UND.Windows.ell d else W

theorem detBy_gateBad (s a W d : ℕ) (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ) :
    DetBy (gateAtoms c y Q t B (gateLen a W d)) (GateBad CD s a W d c y Q t) := by
  unfold GateBad gateLen
  split_ifs
  · exact detBy_shortBad s c y Q t _
  · exact detBy_longBad s c y Q t _

/-- **`S(χ_ch, i_bin)`**: some finite phase-zero gate ending in the bin on the base characteristic
has its intrinsic bad event. -/
def StatEv (CD : ChartData B τ) (tc tr : ℕ → Bool) (k s a W : ℕ) (l : Label) :
    Set (PNoise CD) :=
  {ω | ∃ d, ∃ i < W, IsGate tc tr k d l.1.1 l.1.2.1 (l.2 * W + (i : ℤ)) ∧
    ω ∈ GateBad CD s a W d l.1.1 l.1.2.1 l.1.2.2 (l.2 * W + (i : ℤ))}

/-- The support of `S`: the `B` lane characteristics of the label in this and the preceding bin
(empty off phase-zero rows). -/
def statSupp (tr : ℕ → Bool) (k B W : ℕ) (l : Label) : Finset (ℤ × UND.Site 6) :=
  if lanePhase tr k l.1.2.1 = 0 then
    ((Finset.range B) ×ˢ (Finset.range (2 * W))).image fun p : ℕ × ℕ =>
      laneAtom l.1.1 l.1.2.1 l.1.2.2 p.1 ((l.2 - 1) * W + (p.2 : ℤ))
  else ∅

theorem gateAtoms_sub_statSupp {tc tr : ℕ → Bool} {k a W d : ℕ} {l : Label} {i : ℕ} (hi : i < W)
    (hg : IsGate tc tr k d l.1.1 l.1.2.1 (l.2 * W + (i : ℤ))) (hn : gateLen a W d ≤ W) :
    gateAtoms l.1.1 l.1.2.1 l.1.2.2 (l.2 * W + (i : ℤ)) B (gateLen a W d) ⊆
      statSupp tr k B W l := by
  intro p hp
  rw [mem_gateAtoms] at hp
  obtain ⟨j, hj, i₂, hi₂, rfl⟩ := hp
  unfold statSupp
  simp only [hg.lanePhase, ↓reduceIte]
  rw [Finset.mem_image]
  refine ⟨(j, i + W - 1 - i₂), Finset.mem_product.2 ⟨Finset.mem_range.2 hj,
    Finset.mem_range.2 (by omega)⟩, ?_⟩
  have e : ((i + W - 1 - i₂ : ℕ) : ℤ) = (i : ℤ) + W - 1 - i₂ := by
    rw [Nat.cast_sub (by omega), Nat.cast_sub (by omega)]
    push_cast; ring
  show laneAtom _ _ _ j _ = _
  rw [e]
  congr 1
  ring

theorem detBy_statEv (tc tr : ℕ → Bool) (k s a W : ℕ) (hn : ∀ d < a, UND.Windows.ell d ≤ W)
    (l : Label) : DetBy (statSupp tr k B W l) (StatEv CD tc tr k s a W l) := by
  intro ω ω₂ h
  show (∃ d, ∃ i < W, IsGate tc tr k d l.1.1 l.1.2.1 (l.2 * W + (i : ℤ)) ∧
      ω ∈ GateBad CD s a W d l.1.1 l.1.2.1 l.1.2.2 (l.2 * W + (i : ℤ))) ↔
    (∃ d, ∃ i < W, IsGate tc tr k d l.1.1 l.1.2.1 (l.2 * W + (i : ℤ)) ∧
      ω₂ ∈ GateBad CD s a W d l.1.1 l.1.2.1 l.1.2.2 (l.2 * W + (i : ℤ)))
  refine exists_congr fun d => exists_congr fun i => and_congr_right fun hi =>
    and_congr_right fun hg => ?_
  have hlen : gateLen a W d ≤ W := by
    unfold gateLen
    split_ifs with hd
    · exact hn d hd
    · exact le_rfl
  exact detBy_gateBad s a W d _ _ _ _ ω ω₂
    (fun p hp => h p (gateAtoms_sub_statSupp hi hg hlen hp))

/-- **Statistical supports within a residue class mod 3 are disjoint** (Lemma 6.1's block
partition of the rows; bins `i ≡ i₂ (mod 3)`, `i ≠ i₂`, are at least three bins apart). -/
theorem statSupp_disjoint (tr : ℕ → Bool) {k B W : ℕ} (hB : B ≤ 4 ^ k) {l l₂ : Label}
    (hne : l ≠ l₂) (hcls : (l.2 : ZMod 3) = (l₂.2 : ZMod 3)) :
    Disjoint (statSupp tr k B W l) (statSupp tr k B W l₂) := by
  unfold statSupp
  split_ifs with h1 h2 h2
  · rw [Finset.disjoint_left]
    intro p hp hp₂
    rw [Finset.mem_image] at hp hp₂
    obtain ⟨⟨j, a⟩, hja, rfl⟩ := hp
    obtain ⟨⟨j₂, a₂⟩, hja₂, h⟩ := hp₂
    rw [Finset.mem_product, Finset.mem_range, Finset.mem_range] at hja hja₂
    obtain ⟨ht, hc, hy, hQ⟩ := laneAtom_inj h
    obtain ⟨hy₂, -⟩ := phaseZero_block h2 h1 (by omega) (by omega) hy
    have ha1 : (a : ℤ) < 2 * W := by exact_mod_cast hja.2
    have ha2 : (a₂ : ℤ) < 2 * W := by exact_mod_cast hja₂.2
    have hd3 : (3 : ℤ) ∣ l₂.2 - l.2 := by
      have := (ZMod.intCast_eq_intCast_iff_dvd_sub l.2 l₂.2 3).1 hcls
      exact_mod_cast this
    have hlt : |l₂.2 - l.2| < 3 := by
      rw [abs_lt]
      constructor
      · by_contra hb
        push Not at hb
        nlinarith [(Nat.cast_nonneg a : (0 : ℤ) ≤ a), (Nat.cast_nonneg a₂ : (0 : ℤ) ≤ a₂)]
      · by_contra hb
        push Not at hb
        nlinarith [(Nat.cast_nonneg a : (0 : ℤ) ≤ a), (Nat.cast_nonneg a₂ : (0 : ℤ) ≤ a₂)]
    have hbin := Int.eq_zero_of_abs_lt_dvd hd3 hlt
    exact hne (Prod.ext (Prod.ext hc.symm (Prod.ext hy₂.symm hQ.symm)) (by linarith))
  · exact Finset.disjoint_empty_right _
  · exact Finset.disjoint_empty_left _
  · exact Finset.disjoint_empty_left _

end Bins

/-! ## Lemma 6.2 per bin and Lemma 6.3 for the automaton -/

section Instance

open UND.Rule UPD.Scaffold UND.Chart

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData B τ}

/-- **Lemma 6.2, the bin bound**: in any `W`-time bin on one base characteristic, the probability
that some finite phase-zero gate ending there has its intrinsic bad event is at most
`3u_B/(1 - 4z_B) + 2w_B = η̂_B` (at most `4^r ≤ 3·4^r` short ends of rank offset `r`, each
`≤ u_B z_B^r`; at most one `≤ 2` long end, `≤ w_B`; one depth per row). -/
theorem statEv_le (G : (ISite → PhysSym CD) → (ISite → PhysSym CD)) (N : Finset ISite)
    {C ε : ℝ} {a W s : ℕ} (hR : Regime C ε a W s B)
    (hz : 4 * (2 : ℝ) ^ (-⌊(B : ℝ) * C / 3⌋) < 1) (tc tr : ℕ → Bool) (k : ℕ) (l : Label) :
    (pLaw G N ε).real (StatEv CD tc tr k s a W l) ≤
      3 * (2 : ℝ) ^ (-⌊3 * (B : ℝ) * C / 100⌋) / (1 - 4 * (2 : ℝ) ^ (-⌊(B : ℝ) * C / 3⌋)) +
        2 * (2 : ℝ) ^ (-⌊(B : ℝ) * C ^ 2 / 50⌋) := by
  set u : ℝ := (2 : ℝ) ^ (-⌊3 * (B : ℝ) * C / 100⌋) with hu
  set z : ℝ := (2 : ℝ) ^ (-⌊(B : ℝ) * C / 3⌋) with hz'
  set w : ℝ := (2 : ℝ) ^ (-⌊(B : ℝ) * C ^ 2 / 50⌋) with hw
  have hu0 : 0 ≤ u := by positivity
  have hz0 : 0 ≤ z := by positivity
  have hw0 : 0 ≤ w := by positivity
  have h1z : 0 < 1 - 4 * z := by linarith
  have h3u : 0 ≤ 3 * u / (1 - 4 * z) := div_nonneg (by positivity) h1z.le
  have hu3 : u ≤ 3 * u / (1 - 4 * z) := by
    rw [le_div_iff₀ h1z]; nlinarith
  set μ := pLaw G N ε with hμ
  have hμP : IsProbabilityMeasure μ := isProbabilityMeasure_pLaw G N hR.eps_nonneg hR.eps_le
  by_cases hrow : ∃ d, k ≤ d ∧ IsLeftEnd (phaseOffsets tr) d l.1.2.1
  swap
  · have he : StatEv CD tc tr k s a W l = ∅ := by
      ext ω
      simp only [StatEv, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      rintro ⟨d, i, -, hg, -⟩
      exact hrow ⟨d, hg.1, hg.2.1⟩
    rw [he, measureReal_empty]
    positivity
  obtain ⟨d₀, hkd, hd₀⟩ := hrow
  set E := (Finset.range W).filter fun i : ℕ =>
    IsRightEnd (phaseOffsets tc) d₀ ((l.1.1 + l.2 * W) + i) with hE
  have hsub : StatEv CD tc tr k s a W l ⊆
      ⋃ i ∈ E, GateBad CD s a W d₀ l.1.1 l.1.2.1 l.1.2.2 (l.2 * W + (i : ℤ)) := by
    rintro ω ⟨d, i, hi, hg, hω⟩
    obtain rfl : d = d₀ := depth_unique tr hg.2.1 hd₀
    simp only [Set.mem_iUnion]
    refine ⟨i, Finset.mem_filter.2 ⟨Finset.mem_range.2 hi, ?_⟩, hω⟩
    have := hg.2.2
    rwa [← add_assoc] at this
  have hb : ∀ b : ℝ, (∀ i ∈ E,
      μ.real (GateBad CD s a W d₀ l.1.1 l.1.2.1 l.1.2.2 (l.2 * W + (i : ℤ))) ≤ b) →
      μ.real (StatEv CD tc tr k s a W l) ≤ E.card * b := by
    intro b hb
    calc μ.real (StatEv CD tc tr k s a W l)
        ≤ μ.real (⋃ i ∈ E, GateBad CD s a W d₀ l.1.1 l.1.2.1 l.1.2.2 (l.2 * W + (i : ℤ))) :=
          measureReal_mono hsub (measure_ne_top _ _)
      _ ≤ ∑ i ∈ E, μ.real (GateBad CD s a W d₀ l.1.1 l.1.2.1 l.1.2.2 (l.2 * W + (i : ℤ))) :=
          measureReal_biUnion_finset_le _ _
      _ ≤ ∑ _i ∈ E, b := Finset.sum_le_sum hb
      _ = E.card * b := by rw [Finset.sum_const, nsmul_eq_mul]
  by_cases hda : d₀ < a
  · -- short gates of rank offset `r = a - 1 - d₀`
    set r := a - 1 - d₀ with hr
    have hcard : E.card ≤ 4 ^ r := card_ends_le _ d₀ _ (by
      calc W ≤ 4 ^ a := hR.W_le_four
        _ = 4 ^ (d₀ + 1) * 4 ^ r := by rw [← pow_add]; congr 1; omega)
    have hgate : ∀ i ∈ E,
        μ.real (GateBad CD s a W d₀ l.1.1 l.1.2.1 l.1.2.2 (l.2 * W + (i : ℤ))) ≤ u * z ^ r := by
      intro i _
      simp only [GateBad, hda, ↓reduceIte]
      refine shortBad_le G N hR.eps_nonneg hR.eps_le hR.C_pos r _ ?_ hR.s_ge _ _ _ _
      have h1 := upper_mean_le hR.eps_nonneg hR.eps_le (UND.Windows.ell d₀)
      have h2 := short_support_lt hR.C_pos hR.eps_nonneg hR.a_ge (r := r) (by omega) hR.eps_lt
      rw [show a - 1 - r = d₀ by omega] at h2
      linarith
    refine (hb _ hgate).trans ?_
    have hc : (E.card : ℝ) ≤ 4 ^ r := by exact_mod_cast hcard
    have h4z : (4 * z) ^ r ≤ 1 := pow_le_one₀ (by positivity) (by linarith)
    have h4z0 : 0 ≤ (4 * z) ^ r := by positivity
    calc (E.card : ℝ) * (u * z ^ r) ≤ 4 ^ r * (u * z ^ r) :=
          mul_le_mul_of_nonneg_right hc (by positivity)
      _ = u * (4 * z) ^ r := by rw [mul_pow]; ring
      _ ≤ u := by nlinarith
      _ ≤ 3 * u / (1 - 4 * z) + 2 * w := by linarith
  · -- long gates
    have hcard : E.card ≤ 1 := card_ends_le _ d₀ _ (by
      have h1 := hR.W_le_four
      have h2 : 4 ^ a ≤ 4 ^ (d₀ + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega)
    have hgate : ∀ i ∈ E,
        μ.real (GateBad CD s a W d₀ l.1.1 l.1.2.1 l.1.2.2 (l.2 * W + (i : ℤ))) ≤ w := by
      intro i _
      simp only [GateBad, hda, ↓reduceIte]
      refine longBad_le G N hR.eps_nonneg hR.eps_le hR.C_pos W ?_ hR.s_le _ _ _ _
      exact (lower_law_gt hR.C_pos hR.C_le hR.eps_le hR.epsW_ge).le
    refine (hb _ hgate).trans ?_
    have hc : (E.card : ℝ) ≤ 1 := by exact_mod_cast hcard
    have : (E.card : ℝ) * w ≤ w := by nlinarith
    linarith

/-- **Lemma 6.3 (joint source bound)** for the automaton's noise: for any finite set `L` of source
labels, `P{R ∪ S at all labels of L} ≤ (√C + η̂_B^{1/6})^{|L|}`. -/
theorem joint_source_bound (G : (ISite → PhysSym CD) → (ISite → PhysSym CD)) (N : Finset ISite)
    {C ε : ℝ} {a W s k : ℕ} (hR : Regime C ε a W s B) (hB : B ≤ 4 ^ k)
    (hz : 4 * (2 : ℝ) ^ (-⌊(B : ℝ) * C / 3⌋) < 1)
    (hη1 : 3 * (2 : ℝ) ^ (-⌊3 * (B : ℝ) * C / 100⌋) / (1 - 4 * (2 : ℝ) ^ (-⌊(B : ℝ) * C / 3⌋)) +
        2 * (2 : ℝ) ^ (-⌊(B : ℝ) * C ^ 2 / 50⌋) ≤ 1)
    (tc tr : ℕ → Bool) (L : Finset Label) :
    (pLaw G N ε).real
        (⋂ l ∈ L, (RawEv CD W l ∪ StatEv CD tc tr k s a W l)) ≤
      (√C + (3 * (2 : ℝ) ^ (-⌊3 * (B : ℝ) * C / 100⌋) /
        (1 - 4 * (2 : ℝ) ^ (-⌊(B : ℝ) * C / 3⌋)) +
          2 * (2 : ℝ) ^ (-⌊(B : ℝ) * C ^ 2 / 50⌋)) ^ ((1 : ℝ) / 6)) ^ L.card := by
  have hν := isProbabilityMeasure_noiseSite G N hR.eps_nonneg hR.eps_le
  have : Nonempty (Fin (Fintype.card (PhysSym CD))) := ⟨⟨0, Fintype.card_pos⟩⟩
  have hS := statEv_le G N hR hz tc tr k
  have hRaw := rawEv_le G N hR.eps_nonneg hR.eps_le W
  have h1z : 0 < 1 - 4 * (2 : ℝ) ^ (-⌊(B : ℝ) * C / 3⌋) := by linarith
  have hη0 : 0 ≤ 3 * (2 : ℝ) ^ (-⌊3 * (B : ℝ) * C / 100⌋) /
      (1 - 4 * (2 : ℝ) ^ (-⌊(B : ℝ) * C / 3⌋)) + 2 * (2 : ℝ) ^ (-⌊(B : ℝ) * C ^ 2 / 50⌋) :=
    add_nonneg (div_nonneg (by positivity) h1z.le) (by positivity)
  have hdet := detBy_statEv (CD := CD) tc tr k s a W (fun d hd => hR.ell_le hd)
  rw [pLaw_eq] at hS hRaw ⊢
  exact joint_bound L (RawEv CD W) (StatEv CD tc tr k s a W) (fun l => (rawList W l).toFinset)
    (statSupp tr k B W) (fun l => measurableSet_of_detBy (detBy_rideEv _ _))
    (fun l => measurableSet_of_detBy (hdet l)) (fun l => detBy_rideEv _ _) hdet
    (fun l _ l₂ _ h => rawSupp_disjoint W h) (fun l => ((l.2 : ℤ) : ZMod 3))
    (fun l _ l₂ _ h hc => statSupp_disjoint tr hB h hc) hR.C_pos.le hη0 hη1
    (fun l _ => (hRaw l).trans hR.epsW_le) (fun l _ => hS l)

end Instance

end UND.Sensors
