/-
# Section 6: Lemma 6.2 at one gate (N3, instantiation)

Node N3 of `BLUEPRINT.md` (Part A.6), NEW.

Paper (Section 6): "A short bad event means at least `s` upper successes. A long bad event means
fewer than `s` successes in this recent-window experiment." Lemma 6.2: "At a single critical gate
of depth `a - 1` or `a` the corresponding probability `ρ_B` is also at most `η̂_B`."

Formalization, at one finite phase-zero gate ending at time `t` on the base characteristic
`(c, y, Q)`, for the automaton's two-sided noise (`caOf G N`, any rule on the physical alphabet):
* `laneCount g c y Q t n ω`: the number of lanes `j < B` whose ideal experiment with the mark
  `g j` along the `n` most recent atoms of lane `j`'s true ride succeeds;
* **`ShortBad`** (`≥ s` upper successes along `n = ℓ_d` atoms) and **`LongBad`** (`< s` lower
  successes along the recent `n = W` atoms); both are determined by `gateAtoms` (`detBy_shortBad`,
  `detBy_longBad`) and measurable;
* `laneInd`, `lanes_iIndep` (Lemma 6.1: the `B` lane indicators of a gate are independent, through
  `iIndepFun_of_detBy` and `ride_disjoint`), `integral_laneInd`;
* **`shortBad_le`** (`≤ 2^{-⌊3BC/100⌋}(2^{-⌊BC/3⌋})^r` when the lane mean `p̄ ≤ .53C4^{-r}` and
  `s ≥ .75CB`, from `short_tail` and (14)) and **`longBad_le`** (`≤ 2^{-⌊BC²/50⌋}` when
  `p_W ≥ .9C` and `s ≤ .8CB`, from `long_tail` and (15));
* `upper_mean_le` (`.99[1 - (1-ε)^n] ≤ ε(n + 1)`), so with `short_support_lt`, the short
  hypothesis holds at depth `d = a - 1 - r` with `n = ℓ_d`.
-/
import UncomputableNoiseDiagram.Sensors.Ownership

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory Real
open scoped ENNReal

namespace UND.Sensors

open UND.Rule

section Gate

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData B τ}

/-- The noise configurations of the automaton on the physical alphabet of `CD`. -/
abbrev PNoise (CD : ChartData B τ) := ℤ × UND.Site 6 → Bool × Fin (Fintype.card (PhysSym CD))

open Classical in
/-- The number of lanes `j < B` whose ideal experiment with mark `g j` along the `n` most recent
atoms of lane `j`'s ride (gate ending at `t` on `(c, y, Q)`) succeeds. -/
def laneCount (g : Fin B → Fin (Fintype.card (PhysSym CD)) → Bool) (c y : ℤ) (Q : Fin 4 → ℤ)
    (t : ℤ) (n : ℕ) (ω : PNoise CD) : ℕ :=
  (Finset.univ.filter fun j : Fin B => ω ∈ RideEv (g j) (ride c y Q j t n)).card

/-- **The short bad event** of a gate: at least `s` upper successes along `n` atoms per lane. -/
def ShortBad (CD : ChartData B τ) (s : ℕ) (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ) (n : ℕ) :
    Set (PNoise CD) :=
  {ω | s ≤ laneCount (fun j => upMark (CD := CD) j) c y Q t n ω}

/-- **The long bad event** of a gate: fewer than `s` lower successes along the recent `n` atoms. -/
def LongBad (CD : ChartData B τ) (s : ℕ) (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ) (n : ℕ) :
    Set (PNoise CD) :=
  {ω | laneCount (fun j => loMark (CD := CD) j) c y Q t n ω < s}

theorem laneCount_congr (g : Fin B → Fin (Fintype.card (PhysSym CD)) → Bool) (c y : ℤ)
    (Q : Fin 4 → ℤ) (t : ℤ) (n : ℕ) {ω ω' : PNoise CD}
    (h : ∀ p ∈ gateAtoms c y Q t B n, ω p = ω' p) :
    laneCount g c y Q t n ω = laneCount g c y Q t n ω' := by
  classical
  unfold laneCount
  congr 1
  refine Finset.filter_congr fun j _ => ?_
  refine detBy_rideEv (g j) _ ω ω' fun p hp => h p ?_
  rw [mem_gateAtoms]
  rw [List.mem_toFinset, mem_ride] at hp
  obtain ⟨i, hi, rfl⟩ := hp
  exact ⟨j, j.2, i, hi, rfl⟩

theorem detBy_shortBad (s : ℕ) (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ) (n : ℕ) :
    DetBy (gateAtoms c y Q t B n) (ShortBad CD s c y Q t n) := by
  intro ω ω' h
  show s ≤ laneCount _ c y Q t n ω ↔ s ≤ laneCount _ c y Q t n ω'
  rw [laneCount_congr _ c y Q t n h]

theorem detBy_longBad (s : ℕ) (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ) (n : ℕ) :
    DetBy (gateAtoms c y Q t B n) (LongBad CD s c y Q t n) := by
  intro ω ω' h
  show laneCount _ c y Q t n ω < s ↔ laneCount _ c y Q t n ω' < s
  rw [laneCount_congr _ c y Q t n h]

/-- The success indicator of lane `j`. -/
def laneInd (g : Fin B → Fin (Fintype.card (PhysSym CD)) → Bool) (c y : ℤ) (Q : Fin 4 → ℤ)
    (t : ℤ) (n : ℕ) (j : Fin B) : PNoise CD → ℝ :=
  (RideEv (g j) (ride c y Q j t n)).indicator 1

theorem laneInd_zero_one (g : Fin B → Fin (Fintype.card (PhysSym CD)) → Bool) (c y : ℤ)
    (Q : Fin 4 → ℤ) (t : ℤ) (n : ℕ) (j : Fin B) (ω : PNoise CD) :
    laneInd g c y Q t n j ω = 0 ∨ laneInd g c y Q t n j ω = 1 := by
  unfold laneInd
  by_cases h : ω ∈ RideEv (g j) (ride c y Q j t n)
  · right; simp [Set.indicator_of_mem h]
  · left; simp [Set.indicator_of_notMem h]

theorem measurable_laneInd (g : Fin B → Fin (Fintype.card (PhysSym CD)) → Bool) (c y : ℤ)
    (Q : Fin 4 → ℤ) (t : ℤ) (n : ℕ) (j : Fin B) : Measurable (laneInd g c y Q t n j) :=
  measurable_one.indicator (measurableSet_rideEv (g j) (Set.toFinite _).measurableSet _)

theorem sum_laneInd (g : Fin B → Fin (Fintype.card (PhysSym CD)) → Bool) (c y : ℤ)
    (Q : Fin 4 → ℤ) (t : ℤ) (n : ℕ) (ω : PNoise CD) :
    ∑ j ∈ Finset.univ, laneInd g c y Q t n j ω = (laneCount g c y Q t n ω : ℝ) := by
  classical
  unfold laneInd laneCount
  simp only [Set.indicator_apply, Pi.one_apply]
  rw [Finset.sum_boole]

/-- **Lemma 6.1, independent lanes**: the `B` lane indicators of one gate are independent under
the product noise law. -/
theorem lanes_iIndep {P : ℤ × UND.Site 6 → Measure (Bool × Fin (Fintype.card (PhysSym CD)))}
    [∀ i, IsProbabilityMeasure (P i)] (g : Fin B → Fin (Fintype.card (PhysSym CD)) → Bool)
    (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ) (n : ℕ) :
    iIndepFun (laneInd g c y Q t n) (Measure.infinitePi P) := by
  classical
  refine iIndepFun_of_detBy (fun j : Fin B => (ride c y Q j t n).toFinset) ?_ _
    (measurable_laneInd g c y Q t n) ?_
  · intro j j' hjj
    exact ride_disjoint c y Q t n (fun h => hjj (Fin.ext h))
  · intro j ω ω' h
    unfold laneInd
    simp only [Set.indicator_apply, Pi.one_apply]
    rw [detBy_rideEv (g j) _ ω ω' h]

/-- `.99[1 - (1 - ε)^n] ≤ ε(n + 1)`. -/
theorem upper_mean_le {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (n : ℕ) :
    99 / 100 * (1 - (1 - ε) ^ n) ≤ ε * (n + 1) := by
  have hb := one_add_mul_le_pow (a := -ε) (by linarith) n
  have hn : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have hp : 0 ≤ (1 - ε) ^ n := pow_nonneg (by linarith) n
  have e : (1 + -ε) = 1 - ε := by ring
  rw [e] at hb
  nlinarith

/-- **Lemma 6.2 at a short gate**, for any product noise law: if each lane's upper success
probability is at most `.53C4^{-r}` and `s ≥ .75CB`, the short bad event has probability at most
`2^{-⌊3BC/100⌋}(2^{-⌊BC/3⌋})^r`. -/
theorem shortBad_le_of {ν : Measure (Bool × Fin (Fintype.card (PhysSym CD)))}
    [hν : IsProbabilityMeasure ν] {C : ℝ} (hC : 0 < C) (r : ℕ) (n : ℕ) {s : ℕ}
    (hs : 3 / 4 * C * B ≤ s) (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ)
    (hp : ∀ j : Fin B, (Measure.infinitePi fun _ : ℤ × UND.Site 6 => ν).real
      (RideEv (upMark (CD := CD) j) (ride c y Q j t n)) ≤ 53 / 100 * C * (4 : ℝ)⁻¹ ^ r) :
    (Measure.infinitePi fun _ : ℤ × UND.Site 6 => ν).real (ShortBad CD s c y Q t n) ≤
      (2 : ℝ) ^ (-⌊3 * (B : ℝ) * C / 100⌋) * ((2 : ℝ) ^ (-⌊(B : ℝ) * C / 3⌋)) ^ r := by
  set μ := Measure.infinitePi fun _ : ℤ × UND.Site 6 => ν with hμ
  have hind : iIndepFun (laneInd (fun j => upMark (CD := CD) j) c y Q t n) μ :=
    lanes_iIndep _ c y Q t n
  have hmean : ∀ j ∈ (Finset.univ : Finset (Fin B)),
      μ[laneInd (fun j => upMark (CD := CD) j) c y Q t n j] ≤ 53 / 100 * C * (4 : ℝ)⁻¹ ^ r := by
    intro j _
    unfold laneInd
    rw [integral_indicator_one (measurableSet_rideEv _ (Set.toFinite _).measurableSet _)]
    exact hp j
  have hcard : ((Finset.univ : Finset (Fin B)).card : ℝ) = B := by simp
  have hs' : 3 / 4 * C * ((Finset.univ : Finset (Fin B)).card : ℝ) ≤ (s : ℝ) := by
    rw [hcard]; exact hs
  have h := short_tail hind (measurable_laneInd _ c y Q t n) (laneInd_zero_one _ c y Q t n)
    Finset.univ hC r hmean hs'
  rw [hcard] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext ω
  show s ≤ laneCount _ c y Q t n ω ↔ (s : ℝ) ≤ ∑ j ∈ Finset.univ, laneInd _ c y Q t n j ω
  rw [sum_laneInd]
  exact_mod_cast Iff.rfl

/-- **Lemma 6.2 at a long gate**, for any product noise law: if each lane's lower success
probability is at least `.9C` and `s ≤ .8CB`, the long bad event has probability at most
`2^{-⌊BC²/50⌋}`. -/
theorem longBad_le_of {ν : Measure (Bool × Fin (Fintype.card (PhysSym CD)))}
    [hν : IsProbabilityMeasure ν] {C : ℝ} (hC : 0 < C) (n : ℕ) {s : ℕ}
    (hs : (s : ℝ) ≤ 8 / 10 * C * B) (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ)
    (hq : ∀ j : Fin B, 9 / 10 * C ≤ (Measure.infinitePi fun _ : ℤ × UND.Site 6 => ν).real
      (RideEv (loMark (CD := CD) j) (ride c y Q j t n))) :
    (Measure.infinitePi fun _ : ℤ × UND.Site 6 => ν).real (LongBad CD s c y Q t n) ≤
      (2 : ℝ) ^ (-⌊(B : ℝ) * C ^ 2 / 50⌋) := by
  set μ := Measure.infinitePi fun _ : ℤ × UND.Site 6 => ν with hμ
  have hind : iIndepFun (laneInd (fun j => loMark (CD := CD) j) c y Q t n) μ :=
    lanes_iIndep _ c y Q t n
  have hmean : ∀ j ∈ (Finset.univ : Finset (Fin B)),
      9 / 10 * C ≤ μ[laneInd (fun j => loMark (CD := CD) j) c y Q t n j] := by
    intro j _
    unfold laneInd
    rw [integral_indicator_one (measurableSet_rideEv _ (Set.toFinite _).measurableSet _)]
    exact hq j
  have hcard : ((Finset.univ : Finset (Fin B)).card : ℝ) = B := by simp
  have hs' : (s : ℝ) ≤ 8 / 10 * C * ((Finset.univ : Finset (Fin B)).card : ℝ) := by
    rw [hcard]; exact hs
  have h := long_tail hind (measurable_laneInd _ c y Q t n) (laneInd_zero_one _ c y Q t n)
    Finset.univ hC hmean hs'
  rw [hcard] at h
  refine le_trans (le_of_eq ?_) h
  congr 1
  ext ω
  show laneCount _ c y Q t n ω < s ↔ ∑ j ∈ Finset.univ, laneInd _ c y Q t n j ω < (s : ℝ)
  rw [sum_laneInd]
  exact_mod_cast Iff.rfl

/-- The automaton's two-sided noise law, as a measure on `PNoise CD`. -/
def pLaw (G : (ISite → PhysSym CD) → (ISite → PhysSym CD)) (N : Finset ISite) (ε : ℝ) :
    Measure (PNoise CD) :=
  (caOf G N).noiseLaw₂ ε

/-- The automaton's two-sided noise law as a product law on `PNoise CD`. -/
theorem pLaw_eq (G : (ISite → PhysSym CD) → (ISite → PhysSym CD)) (N : Finset ISite)
    (ε : ℝ) : pLaw G N ε =
      Measure.infinitePi fun _ : ℤ × UND.Site 6 =>
        ((FNE.flagLaw ε).prod (caOf G N).uniformLaw :
          Measure (Bool × Fin (Fintype.card (PhysSym CD)))) := rfl

theorem isProbabilityMeasure_pLaw (G : (ISite → PhysSym CD) → (ISite → PhysSym CD))
    (N : Finset ISite) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) : IsProbabilityMeasure (pLaw G N ε) :=
  UND.CA.isProbabilityMeasure_noiseLaw₂ (caOf G N) h0 h1

theorem isProbabilityMeasure_noiseSite (G : (ISite → PhysSym CD) → (ISite → PhysSym CD))
    (N : Finset ISite) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) :
    IsProbabilityMeasure ((FNE.flagLaw ε).prod (caOf G N).uniformLaw :
      Measure (Bool × Fin (Fintype.card (PhysSym CD)))) := by
  have hf := FNE.isProbabilityMeasure_flagLaw h0 h1
  have hu := UND.CA.isProbabilityMeasure_uniformLaw (caOf G N)
  exact @Measure.prod.instIsProbabilityMeasure _ _ _ _ _ _ hf hu

/-- **Lemma 6.2 at a short gate** for the automaton's noise: if
`p̄ = .99[1 - (1-ε)^n] ≤ .53C4^{-r}` and `s ≥ .75CB`, the short bad event has probability at
most `2^{-⌊3BC/100⌋}(2^{-⌊BC/3⌋})^r`. -/
theorem shortBad_le (G : (ISite → PhysSym CD) → (ISite → PhysSym CD)) (N : Finset ISite)
    {ε C : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hC : 0 < C) (r : ℕ) (n : ℕ)
    (hp : 99 / 100 * (1 - (1 - ε) ^ n) ≤ 53 / 100 * C * (4 : ℝ)⁻¹ ^ r) {s : ℕ}
    (hs : 3 / 4 * C * B ≤ s) (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ) :
    (pLaw G N ε).real (ShortBad CD s c y Q t n) ≤
      (2 : ℝ) ^ (-⌊3 * (B : ℝ) * C / 100⌋) * ((2 : ℝ) ^ (-⌊(B : ℝ) * C / 3⌋)) ^ r := by
  have := isProbabilityMeasure_noiseSite G N h0 h1
  rw [pLaw_eq]
  refine shortBad_le_of hC r n hs c y Q t fun j => ?_
  have h := upper_law G N j h0 h1 _ (ride_nodup c y Q j t n)
  rw [ride_length] at h
  exact (le_of_eq h).trans hp

/-- **Lemma 6.2 at a long gate** for the automaton's noise: if `p_W = .98[1 - (1-ε)^n] ≥ .9C` and
`s ≤ .8CB`, the long bad event has probability at most `2^{-⌊BC²/50⌋}`. -/
theorem longBad_le (G : (ISite → PhysSym CD) → (ISite → PhysSym CD)) (N : Finset ISite)
    {ε C : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (hC : 0 < C) (n : ℕ)
    (hq : 9 / 10 * C ≤ 98 / 100 * (1 - (1 - ε) ^ n)) {s : ℕ} (hs : (s : ℝ) ≤ 8 / 10 * C * B)
    (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ) :
    (pLaw G N ε).real (LongBad CD s c y Q t n) ≤
      (2 : ℝ) ^ (-⌊(B : ℝ) * C ^ 2 / 50⌋) := by
  have := isProbabilityMeasure_noiseSite G N h0 h1
  rw [pLaw_eq]
  refine longBad_le_of hC n hs c y Q t fun j => ?_
  have h := lower_law G N j h0 h1 _ (ride_nodup c y Q j t n)
  rw [ride_length] at h
  exact hq.trans (le_of_eq h.symm)

end Gate

end UND.Sensors
