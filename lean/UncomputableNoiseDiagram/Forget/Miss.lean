/-
# Section 8.1: complete trajectories and their helpers (F1, first step)

Part of node F1 of `BLUEPRINT.md` (Part A.8), NEW.

Paper (Lemma 8.1, proof): "In the absence of a wrong live deep instruction along the ride, the
actual interval contains the ideal upper bit at every step … The proof is simultaneous over
complete trajectories, with no stationarity or independence of their charts assumed."

Formalization (first step): the helper fields of every complete trajectory of the automaton (6),
decoded to `ℤ² × ℤ⁴`, follow (4) off flags and the replacement mark at flags at every integer time
(**`helperTraj_of_complete`**), so the helper-ride lemmas of `Memory/Ride.lean` (`ride_copy`,
`ride_short`, `gate_J`, `hcount_short`, `lcount_long`) apply to complete trajectories; the data
follow the proposal off flags (**`data_of_complete`**).
-/
import UncomputableNoiseDiagram.Memory.Ride
import UncomputableNoiseDiagram.Contour.Coherence

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UND.Forget

open UND.Rule UND.Sensors UND.Memory
open FNE (Plane)

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ]

/-- **The helpers of a complete trajectory follow (4)** off flags and the replacement mark at flags,
at every integer time (`B ≥ 1`). -/
theorem helperTraj_of_complete (CD : ChartData B τ) (s : ℕ) (hB : 1 ≤ B)
    {ω : (ruleCA CD s).Noise₂} {X : ℤ → (ruleCA CD s).Config}
    (hX : (ruleCA CD s).IsComplete ω X) :
    HelperTraj s (fun t => decodeConfig (X t)) ω := by
  intro t w
  have h := hX (t - 1)
  rw [sub_add_cancel] at h
  have key := congrFun (update_decode (proposal (CD := CD) s) (nbhdP B)
    (fun x a => proposal_translate s x a) (fun _ _ _ hh => proposal_local s hB hh)
    (fun v => ω (t, v)) (X (t - 1))) w
  show (decodeConfig (X t) w).2.2 = _
  rw [h]
  refine (congrArg (fun x : PhysSym CD => x.2.2) key).trans ?_
  by_cases hf : (ω (t, siteEquiv.symm w)).1 = true
  · have hf' : flagAt ω t w = true := hf
    simp only [hf, hf', ↓reduceIte]
    rfl
  · have hf' : ¬ flagAt ω t w = true := hf
    simp only [hf, hf', ↓reduceIte, Bool.false_eq_true]

/-- The data of a complete trajectory follow the proposal off flags. -/
theorem data_of_complete (CD : ChartData B τ) (s : ℕ) (hB : 1 ≤ B)
    {ω : (ruleCA CD s).Noise₂} {X : ℤ → (ruleCA CD s).Config}
    (hX : (ruleCA CD s).IsComplete ω X) (t : ℤ) (w : ISite) (hf : flagAt ω t w = false) :
    dataOf (decodeConfig (X t)) w = (proposal s (decodeConfig (X (t - 1))) w).1 := by
  have h := UND.Coh.isFlagTraj_of_complete CD s hB hX t w (by
    show ¬ (ω (t, siteEquiv.symm w)).1 = true
    have : flagAt ω t w = false := hf
    simpa [flagAt] using this)
  exact congrArg Prod.fst h


/-! ## Monotone rides (Lemma 8.1, proof) -/

/- D21: `T = 500` stays opaque wherever `F_R^[T]` (the deep driver) appears in goals. -/
attribute [local irreducible] UND.Param.T

variable {CD : ChartData B τ}

/-- Inclusion of represented intervals, `I ⊆ J`. -/
def isub : Ival → Ival → Bool
  | .zero, .zero => true
  | .zero, .both => true
  | .one, .one => true
  | .one, .both => true
  | .both, .both => true
  | _, _ => false

theorem isub_refl (I : Ival) : isub I I = true := by cases I <;> rfl

theorem isub_both (I : Ival) : isub I .both = true := by cases I <;> rfl

theorem isub_withZero {I J : Ival} (h : isub I J = true) : isub I J.withZero = true := by
  revert h; cases I <;> cases J <;> decide

theorem isub_zero_withZero (J : Ival) : isub .zero J.withZero = true := by cases J <;> rfl

theorem hasOne_of_isub {I J : Ival} (h : isub I J = true) (hI : I.hasOne = true) :
    J.hasOne = true := by
  revert h hI; cases I <;> cases J <;> decide

theorem eq_one_of_isub {I : Ival} (h : isub I .one = true) : I = .one := by
  revert h; cases I <;> decide

/-- The drivers at the base point at time `t'` of the characteristic allow monotone copying: the
ordinary driver is `⊥` (UNKNOWN), or it is live and the deep driver is `⊥` (union with `{0}`) or
live with origin status `o`. -/
def GoodAt (Y : ℤ → PConfig CD) (c y : ℤ) (Q : Fin 4 → ℤ) (t' : ℤ) (o : Bool) : Prop :=
  drvA (Y (t' - 1)) (chSite c y Q t') = none ∨
    ((∃ a, drvA (Y (t' - 1)) (chSite c y Q t') = some a) ∧
      (drvQ (Y (t' - 1)) (chSite c y Q t') = none ∨
        ∃ q, drvQ (Y (t' - 1)) (chSite c y Q t') = some q ∧ CD.orig (ctr CD.toWangRel q) = o))

/-- One monotone copy step: if the ideal value `D` lies in the old interval, the ideal value after
the step (the mark at a flag, `D` otherwise) lies in the new interval. -/
theorem mono_step {s : ℕ} {Y : ℤ → PConfig CD} {ω : PNoise CD} (hY : HelperTraj s Y ω)
    {c y : ℤ} {Q : Fin 4 → ℤ} {t' : ℤ} (hG : GoodAt Y c y Q t' false) (j : Fin B) (D : Ival)
    (hD : isub D (Helper.rep ((Y (t' - 1) (chSite c (y + j) Q (t' - 1))).2.2 j)) = true) :
    isub (rideVal ω j D [laneAtom c y Q j t'])
      (Helper.rep ((Y t' (chSite c (y + j) Q t')).2.2 j)) = true := by
  rw [rep_field hY]
  simp only [rideVal, laneAtom_eq, flagAt, markAt]
  by_cases hf : (ω (t', siteEquiv.symm (chSite c (y + ↑↑j) Q t'))).1 = true
  · simp only [hf, ↓reduceIte]
    exact isub_refl _
  · simp only [hf, ↓reduceIte, Bool.false_eq_true]
    unfold Jf
    rw [chSite_sub_jy, chSite_pred]
    rcases hG with hA | ⟨⟨a, hA⟩, hQ | ⟨q, hQ, ho⟩⟩
    · rw [hA]
      exact isub_both _
    · rw [hA, hQ]
      exact isub_withZero hD
    · rw [hA, hQ]
      simp only [Jof, ho, Bool.false_eq_true, ↓reduceIte]
      exact hD

/-- The origin step: the reset `{0}` (or the mark at a flag) lies in the new interval. -/
theorem mono_origin {s : ℕ} {Y : ℤ → PConfig CD} {ω : PNoise CD} (hY : HelperTraj s Y ω)
    {c y : ℤ} {Q : Fin 4 → ℤ} {t' : ℤ} (hG : GoodAt Y c y Q t' true) (j : Fin B) :
    isub (rideVal ω j .zero [laneAtom c y Q j t'])
      (Helper.rep ((Y t' (chSite c (y + j) Q t')).2.2 j)) = true := by
  rw [rep_field hY]
  simp only [rideVal, laneAtom_eq, flagAt, markAt]
  by_cases hf : (ω (t', siteEquiv.symm (chSite c (y + ↑↑j) Q t'))).1 = true
  · simp only [hf, ↓reduceIte]
    exact isub_refl _
  · simp only [hf, ↓reduceIte, Bool.false_eq_true]
    unfold Jf
    rw [chSite_sub_jy]
    rcases hG with hA | ⟨⟨a, hA⟩, hQ | ⟨q, hQ, ho⟩⟩
    · rw [hA]
      exact isub_both _
    · rw [hA, hQ]
      exact isub_zero_withZero _
    · rw [hA, hQ]
      simp only [Jof, ho, ↓reduceIte]
      rfl

/-- **The monotone ride**: along `n` bases with monotone drivers and no origin, the ideal value
(the most recent mark along the `n` atoms, or `D`) lies in the end input interval whenever `D`
lies in the interval `n` steps earlier. -/
theorem ride_mono {s : ℕ} {Y : ℤ → PConfig CD} {ω : PNoise CD} (hY : HelperTraj s Y ω)
    (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ) (j : Fin B) :
    ∀ n : ℕ, (∀ i < n, GoodAt Y c y Q (t - 1 - i) false) → ∀ D : Ival,
      isub D (Helper.rep ((Y (t - 1 - n) (chSite c (y + j) Q (t - 1 - n))).2.2 j)) = true →
      isub (rideVal ω j D (ride c y Q j t n))
        (Helper.rep ((Y (t - 1) (chSite c (y + j) Q (t - 1))).2.2 j)) = true
  | 0 => fun _ D hD => by simpa [ride, rideVal] using hD
  | n + 1 => by
    intro h D hD
    rw [ride_succ, rideVal_append]
    refine ride_mono hY c y Q t j n (fun i hi => h i (by omega)) _ ?_
    refine mono_step hY (h n (Nat.lt_succ_self n)) j D ?_
    have e : t - 1 - (n : ℤ) - 1 = t - 1 - ((n + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e]
    exact hD

/-- **The monotone short ride**: with monotone non-origin drivers at the first `n` bases and an
origin at the next, the ideal upper experiment's interval lies in the end input interval. -/
theorem ride_mono_short {s : ℕ} {Y : ℤ → PConfig CD} {ω : PNoise CD} (hY : HelperTraj s Y ω)
    (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ) (j : Fin B) (n : ℕ)
    (hcopy : ∀ i < n, GoodAt Y c y Q (t - 1 - i) false)
    (horig : GoodAt Y c y Q (t - 1 - n) true) :
    isub (rideVal ω j .zero (ride c y Q j t (n + 1)))
      (Helper.rep ((Y (t - 1) (chSite c (y + j) Q (t - 1))).2.2 j)) = true := by
  rw [ride_succ, rideVal_append]
  exact ride_mono hY c y Q t j n hcopy _ (mono_origin hY horig j)

/-- At a short gate with monotone drivers, `l_w` is at most the number of upper successes along
the true ride (`n + 1` atoms): a field equal to `{1}` contains only its ideal upper bit. -/
theorem lcount_le_short {s : ℕ} {Y : ℤ → PConfig CD} {ω : PNoise CD} (hY : HelperTraj s Y ω)
    {c y : ℤ} {Q : Fin 4 → ℤ} {t : ℤ} (n : ℕ) (hgate : LiveAt Y c y Q t false)
    (hcopy : ∀ i < n, GoodAt Y c y Q (t - 1 - i) false)
    (horig : GoodAt Y c y Q (t - 1 - n) true) :
    lcount (Y (t - 1)) (chSite c y Q t) ≤
      laneCount (fun j => upMark (CD := CD) j) c y Q t (n + 1) ω := by
  classical
  unfold lcount laneCount
  refine Finset.card_le_card fun j hj => ?_
  obtain ⟨hju, hjr⟩ := mem_filter' hj
  refine Finset.mem_filter.2 ⟨hju, ?_⟩
  rw [gate_J hgate j] at hjr
  have h1 := ride_mono_short hY c y Q t j n hcopy horig
  rw [hjr] at h1
  rw [rideEv_up_iff, eq_one_of_isub h1]
  rfl

/-- At a long gate with monotone non-origin drivers along the recent `n` bases, every lane with a
last HIGH mark in the window still allows `1`: the lower successes are at most `h_w`. -/
theorem lo_le_hcount {s : ℕ} {Y : ℤ → PConfig CD} {ω : PNoise CD} (hY : HelperTraj s Y ω)
    {c y : ℤ} {Q : Fin 4 → ℤ} {t : ℤ} (n : ℕ) (hgate : LiveAt Y c y Q t false)
    (hcopy : ∀ i < n, GoodAt Y c y Q (t - 1 - i) false) :
    laneCount (fun j => loMark (CD := CD) j) c y Q t n ω ≤
      hcount (Y (t - 1)) (chSite c y Q t) := by
  classical
  unfold hcount laneCount
  refine Finset.card_le_card fun j hj => ?_
  obtain ⟨hju, hjr⟩ := mem_filter' hj
  refine Finset.mem_filter.2 ⟨hju, ?_⟩
  rw [gate_J hgate j]
  have h1 := ride_mono hY c y Q t j n hcopy _ (isub_refl _)
  rw [rideVal_of_rideEv_lo ω j _ _ hjr] at h1
  exact hasOne_of_isub h1 rfl

/-! ## Lemma 8.1 -/

/-- **Lemma 8.1** (missed-erasure implication), deterministic, for every trajectory whose helpers
follow (4) (in particular every complete trajectory, `helperTraj_of_complete`). At an output
`w = chSite c y Q t` with live ordinary driver and no erasure, where the chart `ch` has a gate
(`End`, lane phase zero, row flag `hb`; the tiles `i ≤ ℓ_d` sites back on the row are origins
exactly for `i = ℓ_d`; short: `ℓ_d ≤ W`, long: `W < ℓ_d`), either the gate's intrinsic bad event
holds (short: `≥ s` upper successes along `ℓ_d` atoms at flag `0`; long: `< s` lower successes
along the recent `W` atoms at flag `1`), or a live deep query at one lag `ℓ ≤ W` on the base
characteristic is wrong (differs from the chart at its planar site). -/
theorem missed_erasure {s : ℕ} {Y : ℤ → PConfig CD} {ω : PNoise CD} (hY : HelperTraj s Y ω)
    (ch : Plane → LiveLetter CD.toWangRel) {c y : ℤ} {Q : Fin 4 → ℤ} {t : ℤ} {d W : ℕ}
    {hb : Bool} {a : LiveLetter CD.toWangRel}
    (hA : drvA (Y (t - 1)) (chSite c y Q t) = some a)
    (hnp : ¬ Pin s (Y (t - 1)) (chSite c y Q t))
    (hph : CD.phase (ctr CD.toWangRel (ch (c + t, y))) = 0)
    (hend : CD.endP (ctr CD.toWangRel (ch (c + t, y))) = true)
    (hrow : CD.hrow (ctr CD.toWangRel (ch (c + t, y))) = hb)
    (horig : ∀ i : ℕ, i ≤ UND.Windows.ell d →
      CD.orig (ctr CD.toWangRel (ch (c + t - i, y))) = decide (i = UND.Windows.ell d))
    (hshort : hb = false → UND.Windows.ell d ≤ W) (hlong : hb = true → W < UND.Windows.ell d) :
    (hb = false ∧ ω ∈ ShortBad CD s c y Q t (UND.Windows.ell d)) ∨
      (hb = true ∧ ω ∈ LongBad CD s c y Q t W) ∨
      ∃ ℓ : ℕ, ℓ ≤ W ∧ ∃ q, drvQ (Y (t - ℓ - 1)) (chSite c y Q (t - ℓ)) = some q ∧
        q ≠ ch (chSite c y Q (t - ℓ)).1 := by
  classical
  have hell := UND.Windows.ell_pos d
  obtain ⟨q, hq⟩ : ∃ q, drvQ (Y (t - 1)) (chSite c y Q t) = some q := by
    cases h : drvQ (Y (t - 1)) (chSite c y Q t) with
    | none => exact absurd (Or.inl h) hnp
    | some q => exact ⟨q, rfl⟩
  by_cases hqc : q = ch (c + t, y)
  swap
  · refine Or.inr (Or.inr ⟨0, Nat.zero_le _, q, ?_, ?_⟩)
    · simpa using hq
    · simpa [chSite] using hqc
  subst hqc
  have htest : ¬ ((CD.hrow (ctr CD.toWangRel (ch (c + t, y))) = true ∧
      s ≤ hcount (Y (t - 1)) (chSite c y Q t)) ∨
      (CD.hrow (ctr CD.toWangRel (ch (c + t, y))) = false ∧
        lcount (Y (t - 1)) (chSite c y Q t) < s)) :=
    fun h => hnp (Or.inr ⟨_, hq, hph, hend, h⟩)
  by_cases hw : ∃ ℓ : ℕ, ℓ ≤ W ∧ ∃ q, drvQ (Y (t - ℓ - 1)) (chSite c y Q (t - ℓ)) = some q ∧
      q ≠ ch (chSite c y Q (t - ℓ)).1
  · exact Or.inr (Or.inr hw)
  have hw' : ∀ ℓ : ℕ, ℓ ≤ W → ∀ q, drvQ (Y (t - ℓ - 1)) (chSite c y Q (t - ℓ)) = some q →
      q = ch (chSite c y Q (t - ℓ)).1 := by
    intro ℓ hℓ q hq'
    by_contra hne
    exact hw ⟨ℓ, hℓ, q, hq', hne⟩
  -- monotone drivers at every lag `i + 1 ≤ min(W, ℓ_d)`
  have hgood : ∀ i : ℕ, i < W → i < UND.Windows.ell d →
      GoodAt Y c y Q (t - 1 - i) (decide (i + 1 = UND.Windows.ell d)) := by
    intro i hiW hid
    have e1 : t - ((i + 1 : ℕ) : ℤ) - 1 = t - 1 - (i : ℤ) - 1 := by push_cast; ring
    have e2 : t - ((i + 1 : ℕ) : ℤ) = t - 1 - (i : ℤ) := by push_cast; ring
    have hwi := hw' (i + 1) (by omega)
    rw [e1, e2] at hwi
    have ho := horig (i + 1) (by omega)
    have e3 : (c + t - ((i + 1 : ℕ) : ℤ), y) = (chSite c y Q (t - 1 - i)).1 := by
      simp only [chSite]
      push_cast
      ring_nf
    rw [e3] at ho
    unfold GoodAt
    cases hAi : drvA (Y (t - 1 - i - 1)) (chSite c y Q (t - 1 - i)) with
    | none => exact Or.inl rfl
    | some a' =>
      refine Or.inr ⟨⟨a', rfl⟩, ?_⟩
      cases hQi : drvQ (Y (t - 1 - i - 1)) (chSite c y Q (t - 1 - i)) with
      | none => exact Or.inl rfl
      | some q' =>
        refine Or.inr ⟨q', rfl, ?_⟩
        rw [hwi q' hQi]
        exact ho
  have hgate : LiveAt Y c y Q t false := by
    refine ⟨a, ch (c + t, y), hA, hq, ?_⟩
    have := horig 0 (Nat.zero_le _)
    simp only [Nat.cast_zero, sub_zero] at this
    rw [this]
    exact decide_eq_false (by omega)
  cases hb with
  | false =>
    have hdW := hshort rfl
    obtain ⟨n, hn⟩ : ∃ n, UND.Windows.ell d = n + 1 := ⟨UND.Windows.ell d - 1, by omega⟩
    have hcopy : ∀ i < n, GoodAt Y c y Q (t - 1 - i) false := by
      intro i hi
      have := hgood i (by omega) (by omega)
      rwa [decide_eq_false (by omega : ¬ i + 1 = UND.Windows.ell d)] at this
    have horig' : GoodAt Y c y Q (t - 1 - n) true := by
      have := hgood n (by omega) (by omega)
      rwa [decide_eq_true (by omega : n + 1 = UND.Windows.ell d)] at this
    have hl := lcount_le_short hY n hgate hcopy horig'
    have hs : s ≤ lcount (Y (t - 1)) (chSite c y Q t) := by
      by_contra hlt
      exact htest (Or.inr ⟨hrow, by omega⟩)
    refine Or.inl ⟨rfl, ?_⟩
    show s ≤ laneCount _ c y Q t (UND.Windows.ell d) ω
    rw [hn]
    omega
  | true =>
    have hdW := hlong rfl
    have hcopy : ∀ i < W, GoodAt Y c y Q (t - 1 - i) false := by
      intro i hi
      have := hgood i hi (by omega)
      rwa [decide_eq_false (by omega : ¬ i + 1 = UND.Windows.ell d)] at this
    have hl := lo_le_hcount hY W hgate hcopy
    have hs : hcount (Y (t - 1)) (chSite c y Q t) < s := by
      by_contra hlt
      exact htest (Or.inl ⟨hrow, by omega⟩)
    refine Or.inr (Or.inl ⟨rfl, ?_⟩)
    show laneCount _ c y Q t W ω < s
    omega

end UND.Forget
