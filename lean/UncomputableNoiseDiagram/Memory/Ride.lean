/-
# The helper ride: actual intervals are the ideal experiment (Mem2, first part)

Node Mem2 of `BLUEPRINT.md` (Part A.7), NEW; also used by Lemma 8.1 (F1).

Paper (Lemma 7.1, proof): "At a short gate with correct flag one, its true origin lies less than
`W` updates earlier. If every ordinary and deep driver since that origin is correct, the reset
followed by copying and raw marks gives exactly the ideal upper experiment. An erasure therefore
requires its intrinsic short failure. … At a long gate with correct flag zero, the true origin is
outside the recent `W` window. If all drivers there are correct, each last HIGH mark forces a
singleton one, whatever the older helper state. Absence of the intrinsic long failure gives at
least `s` such singleton fields, preventing an erasure. … The `B` physical lanes share the same
driver base at every lag by (4)."

Formalization (deterministic, for any trajectory whose helper fields follow (4) off flags and the
replacement mark at flags, `HelperTraj`; the complete trajectories of the automaton are such, and
so is the stationary helper initialization of Section 7):
* `flagAt`, `markAt`; `rep_field` (the represented interval of a field: the mark's at a flag,
  `J_{j,t}(w)` otherwise);
* `rideVal ω j d L`: the interval of the most recent replacement mark along the atoms `L`, or `d`;
  `rideVal_append`, `ride_succ`; `rideEv_up_iff` (`RideEv (upMark j)` is `1 ∈ rideVal … {0}`),
  `rideVal_of_rideEv_lo` (a last HIGH mark gives `{1}` whatever the older state);
* `chSite_sub_jy`, `chSite_pred` (the base of a lane-`j` site is the base characteristic point;
  the copy predecessor is the previous point of the lane characteristic);
* **`ride_copy`**: with live drivers and no origin at the ride's first `n` bases, the interval at
  the end input is `rideVal` over the `n` atoms with the older interval as default;
* **`ride_origin`**: at a base whose live deep driver is an origin the interval is the reset `{0}`
  unless replaced;
* **`ride_short`**: with the origin at the `n`-th base, the end input interval is `rideVal … {0}`
  over the true ride: `1 ∈ J_end ⟺ RideEv (upMark j)`;
* **`gate_J`** (the gate reads `J_{j,t}(w + j e_y)` = the lane's end input interval, the same
  drivers for all lanes), **`hcount_short`** (`h_w` = the number of upper successes: an erasure
  at a correct short gate is the short bad event), **`lcount_long`** (`l_w ≥` the number of lower
  successes in the recent window: absent the long bad event, no erasure).
-/
import UncomputableNoiseDiagram.Sensors.Gate

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UND.Memory

open UND.Rule UND.Sensors

/- D21: `T = 500` stays opaque wherever `F_R^[T]` (the deep driver) appears in goals. -/
attribute [local irreducible] UND.Param.T

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData B τ}

/-- The replacement flag of the output at time `t`, site `w`. -/
def flagAt (ω : PNoise CD) (t : ℤ) (w : ISite) : Bool := (ω (t, siteEquiv.symm w)).1

/-- The replacement mark of the output at time `t`, site `w`. -/
def markAt (ω : PNoise CD) (t : ℤ) (w : ISite) : PhysSym CD :=
  decodeSym (ω (t, siteEquiv.symm w)).2

/-- The helper fields of a trajectory follow (4) off flags and the replacement mark at flags. -/
def HelperTraj (s : ℕ) (Y : ℤ → PConfig CD) (ω : PNoise CD) : Prop :=
  ∀ t w, (Y t w).2.2 =
    if flagAt ω t w = true then (markAt ω t w).2.2 else (proposal s (Y (t - 1)) w).2.2

theorem rep_field {s : ℕ} {Y : ℤ → PConfig CD} {ω : PNoise CD} (hY : HelperTraj s Y ω)
    (t : ℤ) (w : ISite) (j : Fin B) :
    Helper.rep ((Y t w).2.2 j) = if flagAt ω t w = true then Helper.rep ((markAt ω t w).2.2 j)
      else Jf (Y (t - 1)) j w := by
  rw [hY t w]
  by_cases h : flagAt ω t w = true
  · simp only [h, ↓reduceIte]
  · simp only [h, ↓reduceIte, Bool.false_eq_true]
    show Helper.rep ((Jf (Y (t - 1)) j w).repr) = _
    rw [Helper.rep_repr]

/-- The interval of the most recent replacement mark (field `j`) along `L`, or `d`. -/
def rideVal (ω : PNoise CD) (j : Fin B) (d : Ival) : List (ℤ × UND.Site 6) → Ival
  | [] => d
  | a :: L => if (ω a).1 = true then Helper.rep ((decodeSym (ω a).2 : PhysSym CD).2.2 j)
      else rideVal ω j d L

theorem rideVal_append (ω : PNoise CD) (j : Fin B) (d : Ival) :
    ∀ L₁ L₂ : List (ℤ × UND.Site 6),
      rideVal ω j d (L₁ ++ L₂) = rideVal ω j (rideVal ω j d L₂) L₁
  | [], _ => rfl
  | a :: L₁, L₂ => by
    simp only [List.cons_append, rideVal]
    rw [rideVal_append ω j d L₁ L₂]

theorem ride_succ (c y : ℤ) (Q : Fin 4 → ℤ) (j : ℕ) (t : ℤ) (n : ℕ) :
    ride c y Q j t (n + 1) = ride c y Q j t n ++ [laneAtom c y Q j (t - 1 - n)] := by
  simp [ride, List.range_succ]

/-- `RideEv (upMark j)` is `1 ∈` the interval of the most recent mark, with reset default `{0}`. -/
theorem rideEv_up_iff (ω : PNoise CD) (j : Fin B) :
    ∀ L : List (ℤ × UND.Site 6),
      ω ∈ RideEv (upMark (CD := CD) j) L ↔ (rideVal ω j .zero L).hasOne = true
  | [] => by simp [RideEv, rideVal, Ival.hasOne]
  | a :: L => by
    have ih := rideEv_up_iff ω j L
    show ((ω a).1 = true ∧ upMark j (ω a).2 = true) ∨ ((ω a).1 = false ∧ ω ∈ RideEv _ L) ↔ _
    simp only [rideVal]
    by_cases hf : (ω a).1 = true
    · simp only [hf, true_and, Bool.true_eq_false, false_and, or_false, ↓reduceIte, upMark,
        decide_eq_true_eq]
      cases h : Helper.rep ((decodeSym (ω a).2 : PhysSym CD).2.2 j) <;> simp [Ival.hasOne]
    · have hf' : (ω a).1 = false := by simpa using hf
      simp only [hf', Bool.false_eq_true, false_and, true_and, false_or, ↓reduceIte, ih]

/-- A last HIGH mark along `L` gives `{1}`, whatever the older interval. -/
theorem rideVal_of_rideEv_lo (ω : PNoise CD) (j : Fin B) (d : Ival) :
    ∀ L : List (ℤ × UND.Site 6), ω ∈ RideEv (loMark (CD := CD) j) L → rideVal ω j d L = .one
  | [] => fun h => absurd h (Set.notMem_empty _)
  | a :: L => by
    intro h
    rcases h with ⟨hf, hm⟩ | ⟨hf, hL⟩
    · simp only [rideVal, hf, ↓reduceIte]
      simpa [loMark] using hm
    · have hf0 : (ω a).1 = false := hf
      have hf' : ¬ (ω a).1 = true := by simp [hf0]
      simp only [rideVal, hf']
      exact rideVal_of_rideEv_lo ω j d L hL

/-! ## Sites along a ride -/

theorem chSite_sub_jy (c y : ℤ) (Q : Fin 4 → ℤ) (j : ℕ) (t : ℤ) :
    chSite c (y + j) Q t - jy j = chSite c y Q t := by
  simp [chSite, jy]

theorem chSite_pred (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ) :
    chSite c y Q t - ex + vS = chSite c y Q (t - 1) := by
  refine Prod.ext (Prod.ext ?_ ?_) (funext fun i => ?_)
  · simp only [chSite, ex, vS, Prod.fst_add, Prod.fst_sub, Prod.fst_zero]
    ring_nf
  · simp [chSite, ex, vS]
  · simp only [chSite, ex, vS, Prod.snd_add, Prod.snd_sub, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, vP, Pi.zero_apply, smul_eq_mul]
    ring_nf

theorem chSite_add_jy (c y : ℤ) (Q : Fin 4 → ℤ) (j : ℕ) (t : ℤ) :
    chSite c y Q t + jy j = chSite c (y + j) Q t := by
  simp [chSite, jy]

theorem laneAtom_eq (c y : ℤ) (Q : Fin 4 → ℤ) (j : ℕ) (t : ℤ) :
    laneAtom c y Q j t = (t, siteEquiv.symm (chSite c (y + j) Q t)) := rfl

/-- The deep and ordinary drivers at the base point at time `t'` of the characteristic are live, and
the deep driver's centre is (`o = true`) or is not an origin. -/
def LiveAt (Y : ℤ → PConfig CD) (c y : ℤ) (Q : Fin 4 → ℤ) (t' : ℤ) (o : Bool) : Prop :=
  ∃ a q, drvA (Y (t' - 1)) (chSite c y Q t') = some a ∧
    drvQ (Y (t' - 1)) (chSite c y Q t') = some q ∧ CD.orig (ctr CD.toWangRel q) = o

/-- One copy step: with live non-origin drivers at the base, the interval at the lane site is
the mark's at a flag and the copied predecessor's otherwise. -/
theorem copy_step {s : ℕ} {Y : ℤ → PConfig CD} {ω : PNoise CD} (hY : HelperTraj s Y ω)
    {c y : ℤ} {Q : Fin 4 → ℤ} {t' : ℤ} (hL : LiveAt Y c y Q t' false) (j : Fin B) :
    Helper.rep ((Y t' (chSite c (y + j) Q t')).2.2 j) =
      rideVal ω j (Helper.rep ((Y (t' - 1) (chSite c (y + j) Q (t' - 1))).2.2 j))
        [laneAtom c y Q j t'] := by
  obtain ⟨a, q, ha, hq, ho⟩ := hL
  rw [rep_field hY]
  simp only [rideVal, laneAtom_eq, flagAt, markAt]
  by_cases hf : (ω (t', siteEquiv.symm (chSite c (y + ↑↑j) Q t'))).1 = true
  · simp only [hf, ↓reduceIte]
  · simp only [hf, ↓reduceIte, Bool.false_eq_true]
    unfold Jf
    rw [chSite_sub_jy, chSite_pred, ha, hq]
    simp only [Jof, ho, Bool.false_eq_true, ↓reduceIte]
    rfl

/-- The origin step: with live drivers at the base and an origin there, the interval is the reset
`{0}` unless replaced. -/
theorem origin_step {s : ℕ} {Y : ℤ → PConfig CD} {ω : PNoise CD} (hY : HelperTraj s Y ω)
    {c y : ℤ} {Q : Fin 4 → ℤ} {t' : ℤ} (hL : LiveAt Y c y Q t' true) (j : Fin B) :
    Helper.rep ((Y t' (chSite c (y + j) Q t')).2.2 j) =
      rideVal ω j .zero [laneAtom c y Q j t'] := by
  obtain ⟨a, q, ha, hq, ho⟩ := hL
  rw [rep_field hY]
  simp only [rideVal, laneAtom_eq, flagAt, markAt]
  by_cases hf : (ω (t', siteEquiv.symm (chSite c (y + ↑↑j) Q t'))).1 = true
  · simp only [hf, ↓reduceIte]
  · simp only [hf, ↓reduceIte, Bool.false_eq_true]
    unfold Jf
    rw [chSite_sub_jy, ha, hq]
    simp only [Jof, ho, ↓reduceIte]

/-- **Copying along the ride**: with live non-origin drivers at the first `n` bases, the end input
interval of lane `j` is the most recent mark along the `n` atoms, or the older interval. -/
theorem ride_copy {s : ℕ} {Y : ℤ → PConfig CD} {ω : PNoise CD} (hY : HelperTraj s Y ω)
    (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ) (j : Fin B) :
    ∀ n : ℕ, (∀ i < n, LiveAt Y c y Q (t - 1 - i) false) →
      Helper.rep ((Y (t - 1) (chSite c (y + j) Q (t - 1))).2.2 j) =
        rideVal ω j (Helper.rep ((Y (t - 1 - n) (chSite c (y + j) Q (t - 1 - n))).2.2 j))
          (ride c y Q j t n)
  | 0 => fun _ => by simp [ride, rideVal]
  | n + 1 => by
    intro h
    rw [ride_succ, rideVal_append, ride_copy hY c y Q t j n fun i hi => h i (by omega)]
    congr 1
    have hs := copy_step hY (h n (Nat.lt_succ_self n)) j
    rw [hs]
    congr 3
    push_cast
    ring_nf

/-- **The short ride**: with live drivers at the first `n` bases, no origin before the last and an
origin at the last, the end input interval of lane `j` is the ideal upper experiment's. -/
theorem ride_short {s : ℕ} {Y : ℤ → PConfig CD} {ω : PNoise CD} (hY : HelperTraj s Y ω)
    (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ) (j : Fin B) (n : ℕ)
    (hcopy : ∀ i < n, LiveAt Y c y Q (t - 1 - i) false)
    (horig : LiveAt Y c y Q (t - 1 - n) true) :
    Helper.rep ((Y (t - 1) (chSite c (y + j) Q (t - 1))).2.2 j) =
      rideVal ω j .zero (ride c y Q j t (n + 1)) := by
  rw [ride_copy hY c y Q t j n hcopy, ride_succ, rideVal_append, origin_step hY horig j]

/-- **The gate reads its lanes**: at a gate with live drivers and a non-origin deep driver at its
base, `J_{j,t}(w + j e_y)` is the end input interval of lane `j` (the same drivers for all
lanes). -/
theorem gate_J {Y : ℤ → PConfig CD} {c y : ℤ} {Q : Fin 4 → ℤ} {t : ℤ}
    (hL : LiveAt Y c y Q t false) (j : Fin B) :
    Jf (Y (t - 1)) j (chSite c y Q t + jy j) =
      Helper.rep ((Y (t - 1) (chSite c (y + j) Q (t - 1))).2.2 j) := by
  obtain ⟨a, q, ha, hq, ho⟩ := hL
  unfold Jf
  rw [add_sub_cancel_right, ha, hq]
  simp only [Jof, ho, Bool.false_eq_true, ↓reduceIte]
  rw [chSite_add_jy, chSite_pred]
  rfl

theorem mem_filter' {α : Type*} {p : α → Prop} {S : Finset α} {inst : DecidablePred p} {a : α}
    (h : a ∈ @Finset.filter α p inst S) : a ∈ S ∧ p a :=
  (@Finset.mem_filter α p inst S a).mp h

/-- **At a correct short gate `h_w` counts the upper successes**: with live drivers at the gate,
along the first `n` ride bases (no origin) and an origin at the `(n+1)`-st, `h_w` is the number of
lanes whose ideal upper experiment along the `n + 1` atoms succeeds; so `h_w ≥ s` is the short bad
event. -/
theorem hcount_short {s : ℕ} {Y : ℤ → PConfig CD} {ω : PNoise CD} (hY : HelperTraj s Y ω)
    {c y : ℤ} {Q : Fin 4 → ℤ} {t : ℤ} (n : ℕ) (hgate : LiveAt Y c y Q t false)
    (hcopy : ∀ i < n, LiveAt Y c y Q (t - 1 - i) false)
    (horig : LiveAt Y c y Q (t - 1 - n) true) :
    hcount (Y (t - 1)) (chSite c y Q t) =
      laneCount (fun j => upMark (CD := CD) j) c y Q t (n + 1) ω := by
  classical
  unfold hcount laneCount
  congr 1
  refine Finset.filter_congr fun j _ => ?_
  rw [gate_J hgate j, ride_short hY c y Q t j n hcopy horig, ← rideEv_up_iff]

/-- **At a correct long gate `l_w` dominates the lower successes**: with live non-origin drivers
at the gate and along the first `n` ride bases, every lane whose ideal lower experiment along the
`n` most recent atoms succeeds holds `{1}`, whatever the older state. -/
theorem lcount_long {s : ℕ} {Y : ℤ → PConfig CD} {ω : PNoise CD} (hY : HelperTraj s Y ω)
    {c y : ℤ} {Q : Fin 4 → ℤ} {t : ℤ} (n : ℕ) (hgate : LiveAt Y c y Q t false)
    (hcopy : ∀ i < n, LiveAt Y c y Q (t - 1 - i) false) :
    laneCount (fun j => loMark (CD := CD) j) c y Q t n ω ≤
      lcount (Y (t - 1)) (chSite c y Q t) := by
  classical
  unfold lcount laneCount
  refine Finset.card_le_card fun j hj => ?_
  obtain ⟨hju, hjr⟩ := mem_filter' hj
  refine Finset.mem_filter.2 ⟨hju, ?_⟩
  rw [gate_J hgate j, ride_copy hY c y Q t j n hcopy]
  exact rideVal_of_rideEv_lo ω j _ _ hjr

end UND.Memory
