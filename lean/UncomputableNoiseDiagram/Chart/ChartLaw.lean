/-
# Prop 4.3, the nonhalting branch: the translation-invariant chart law (M5)

Part of node M5 of `BLUEPRINT.md` (Part A.4). ADAPTED: the hard-model core's push-forward of Haar
measure by an equivariant map (`UPD.Scaffold.PhaseSystem.isTILaw`, `Background/BgMap.lean`:
`addDig`, `haar_map_addDig`, `ae_typical_addDig`, the `MLevel` measurability calculus); NEW: the
equivariance of our construction is proved directly (no uniqueness theorem is needed).

Paper (Prop 4.3, proof): "Translating and taking a weak limit of spatial averages gives an
invariant law. Its phase is Haar because each finite residue law is invariant under the transitive
integer translations of that residue torus. Hence it gives full measure to typical phases and
retains the cutoff." Formalized route (same law, D32): the image of Haar measure under
`τ ↦ chartOf τ`; it is translation invariant because the chart of `τ + a` is the translate of the
chart of `τ` (`chartOf_shift`) and Haar measure is invariant under `τ ↦ τ + a`; its phase is Haar
by construction.

* digits and parent ranks of a translated phase (`dig_shift`, `prank_iff_dig`, `prankOf_shift`),
  frames of translated offsets (`FShift`, `frameLo_shift`, `inFrame_shift`, `isFree_shift`,
  `zeta_shift`), board inputs and contents (`PShift.cutH_eq`, `PShift.cutPi_eq`, `runP_congr`,
  `PShift.sAt_eq`);
* nearest walls and tags along a translated line (`wdL_shift`, `wdR_shift`, `wtag_shift`,
  `evTag_shift`); `PTrans` (`τ' = τ + a`, `Y_{τ'} = T_a Y_τ`), every field of the construction is
  covariant (`PTrans.oEc`, …, `PTrans.rawVal`), **`chartOf_shift`**: `chart(τ + a) = T_a chart(τ)`;
* D31 (QB, s6): **`measurableSet_typical`**, **`haar_typical`** (`Typical` is measurable and has
  Haar measure one);
* measurability of `τ ↦ chartOf τ` (`mlevel_*`, `measurable_chartOf`);
* `chartLaw`, **`chartLaw_shift`** (translation invariance), `GoodChart` (legal, typical quarter
  phase, cutoff `[r < cut]`), `measurableSet_goodChart`, `ae_goodChart`;
* **`chart_law_exists`** (Prop 4.3, nonhalting branch).
-/
import UncomputableNoiseDiagram.Chart.Construct

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

namespace UND.Chart

open UPD UPD.Scaffold

/-! ## Digits and parent ranks of a translated phase -/

/-- Digits of a translated phase: if `c' ≡ c + s` modulo every `2^l`, the digits of `z` for `c'`
are those of `z - s` for `c`. -/
theorem dig_shift {c c' : ℕ → Bool} {s : ℤ} (h : ∀ l, (2 : ℤ) ^ l ∣ wsum c' l - wsum c l - s)
    (m : ℕ) (z : ℤ) : dig c' m z = dig c m (z - s) := by
  have e1 := emod_eq_wsum_dig c' (m + 1) z
  have e2 := emod_eq_wsum_dig c (m + 1) (z - s)
  have e : (z - wsum c' (m + 1)) % 2 ^ (m + 1) = (z - s - wsum c (m + 1)) % 2 ^ (m + 1) := by
    rw [Int.emod_eq_emod_iff_emod_sub_eq_zero]
    apply Int.emod_eq_zero_of_dvd
    have h' : (z - wsum c' (m + 1)) - (z - s - wsum c (m + 1)) =
        -(wsum c' (m + 1) - wsum c (m + 1) - s) := by ring
    rw [h']
    exact (dvd_neg).2 (h (m + 1))
  rw [e1, e2] at e
  exact prefix_eq_of_wsum_eq e m (by omega)

/-- The parent rank in terms of the digits `ς_{m+1}`. -/
theorem prank_iff_dig (t : ℕ → Bool) (z : ℤ) (r : ℕ) :
    PRank t z r ↔ dig t (r + 1) z = true ∧ ∀ m < r, dig t (m + 1) z = false := by
  simp only [PRank, IsRank, dig_succ]

theorem prank_shift {c c' : ℕ → Bool} {s : ℤ} (h : ∀ l, (2 : ℤ) ^ l ∣ wsum c' l - wsum c l - s)
    (z : ℤ) (r : ℕ) : PRank c' z r ↔ PRank c (z - s) r := by
  simp only [prank_iff_dig, dig_shift h]

theorem prankOf_congr {t t' : ℕ → Bool} {z z' : ℤ} (h : ∀ r, PRank t z r ↔ PRank t' z' r) :
    prankOf t z = prankOf t' z' := by
  classical
  by_cases hex : ∃ r, PRank t z r
  · obtain ⟨r, hr⟩ := hex
    rw [prankOf_eq hr, prankOf_eq ((h r).1 hr)]
  · have hex' : ¬ ∃ r, PRank t' z' r := fun ⟨r, hr⟩ => hex ⟨r, (h r).2 hr⟩
    unfold prankOf
    rw [dite_eq_right hex, dite_eq_right hex']

theorem prankOf_shift {c c' : ℕ → Bool} {s : ℤ}
    (h : ∀ l, (2 : ℤ) ^ l ∣ wsum c' l - wsum c l - s) (z : ℤ) :
    prankOf c' z = prankOf c (z - s) :=
  prankOf_congr (prank_shift h z)

/-! ## Frames of a translated phase -/

/-- Frame offsets of a translated phase: `a' ≡ a + s (mod 4^{d+1})` at every depth. -/
def FShift (a a' : ℕ → ℤ) (s : ℤ) : Prop := ∀ d, (4 : ℤ) ^ (d + 1) ∣ a' d - a d - s

theorem fshift_phase {c c' : ℕ → Bool} {s : ℤ}
    (h : ∀ l, (2 : ℤ) ^ l ∣ wsum c' l - wsum c l - s) :
    FShift (phaseOffsets c) (phaseOffsets c') s := by
  intro d
  have := h (2 * d + 2)
  rwa [show (2 : ℤ) ^ (2 * d + 2) = 4 ^ (d + 1) by
    rw [show 2 * d + 2 = 2 * (d + 1) by ring, pow_mul]; norm_num] at this

/-- The frame index shift at depth `d`. -/
def fq (a a' : ℕ → ℤ) (s : ℤ) (d : ℕ) : ℤ := (a' d - a d - s) / 4 ^ (d + 1)

section FShift

variable {a a' : ℕ → ℤ} {s : ℤ} (h : FShift a a' s)
include h

theorem fq_spec (d : ℕ) : a' d = a d + s + fq a a' s d * 4 ^ (d + 1) := by
  rw [fq, Int.ediv_mul_cancel (h d)]; ring

theorem frameLo_shift (d : ℕ) (m : ℤ) :
    frameLo a' d m = frameLo a d (m + fq a a' s d) + s := by
  simp only [frameLo]
  rw [fq_spec h d, pow_succ]
  ring

theorem frameHi_shift (d : ℕ) (m : ℤ) :
    frameHi a' d m = frameHi a d (m + fq a a' s d) + s := by
  simp only [frameHi]
  rw [fq_spec h d, pow_succ]
  ring

theorem inFrame_shift (d : ℕ) (z : ℤ) : InFrame a' d z ↔ InFrame a d (z - s) := by
  constructor
  · rintro ⟨m, h1, h2⟩
    rw [frameLo_shift h] at h1
    rw [frameHi_shift h] at h2
    exact ⟨m + fq a a' s d, by omega, by omega⟩
  · rintro ⟨m, h1, h2⟩
    refine ⟨m - fq a a' s d, ?_, ?_⟩
    · rw [frameLo_shift h, sub_add_cancel]; omega
    · rw [frameHi_shift h, sub_add_cancel]; omega

theorem isFree_shift (d : ℕ) (m z : ℤ) :
    IsFree a' d m z ↔ IsFree a d (m + fq a a' s d) (z - s) := by
  simp only [IsFree, frameLo_shift h, frameHi_shift h, inFrame_shift h]
  constructor
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega, h3⟩
  · rintro ⟨h1, h2, h3⟩; exact ⟨by omega, by omega, h3⟩

theorem zeta_shift (ha : FrameOffsets a) (ha' : FrameOffsets a') {d : ℕ} (hd : 1 ≤ d) (m : ℤ)
    {i : ℕ} (hi : i < MachineM.Nd d) :
    BG.zeta a' d m i = BG.zeta a d (m + fq a a' s d) i + s := by
  have hc : (BG.freeSet a' d m).card = MachineM.Nd d := BG.card_freeSet ha' hd m
  have hu := Finset.orderEmbOfFin_unique (s := BG.freeSet a' d m)
    (f := fun x : Fin (BG.freeSet a' d m).card => BG.zeta a d (m + fq a a' s d) x.val + s) rfl
    (fun x => BG.mem_freeSet.2 ((isFree_shift h d m _).2 (by
      rw [add_sub_cancel_right]; exact BG.zeta_free ha hd _ (lt_of_lt_of_eq x.2 hc))))
    (fun x y hxy => by
      have := (BG.zeta_lt_iff ha hd (m + fq a a' s d) (lt_of_lt_of_eq x.2 hc)
        (lt_of_lt_of_eq y.2 hc)).2 hxy
      simp only
      omega)
  rw [BG.zeta_eq ha' hd m hi]
  exact (congrFun hu ⟨i, by rw [hc]; exact hi⟩).symm

end FShift

/-! ## Board inputs and contents of a translated phase -/

/-- The phase `τ'` is the translate `τ + a` (`addDig a τ`, `wsum_addDig`). -/
def PShift (τ τ' : ℕ → Bool × Bool) (a : Plane) : Prop :=
  ∀ l, (2 : ℤ) ^ l ∣ wsum (col τ') l - wsum (col τ) l - a.1 ∧
    (2 : ℤ) ^ l ∣ wsum (row τ') l - wsum (row τ) l - a.2

theorem pshift_addDig (a : Plane) (τ : ℕ → Bool × Bool) : PShift τ (addDig a τ) a :=
  wsum_addDig a τ

/-- The column frame index shift. -/
abbrev q1 (τ τ' : ℕ → Bool × Bool) (a : Plane) (d : ℕ) : ℤ := fq (BG.a1 τ) (BG.a1 τ') a.1 d

/-- The row frame index shift. -/
abbrev q2 (τ τ' : ℕ → Bool × Bool) (a : Plane) (d : ℕ) : ℤ := fq (BG.a2 τ) (BG.a2 τ') a.2 d

section PShift

variable {τ τ' : ℕ → Bool × Bool} {a : Plane} (hs : PShift τ τ' a)
include hs

theorem PShift.fcol : FShift (BG.a1 τ) (BG.a1 τ') a.1 := fshift_phase fun l => (hs l).1

theorem PShift.frow : FShift (BG.a2 τ) (BG.a2 τ') a.2 := fshift_phase fun l => (hs l).2

theorem PShift.zeta1 {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {i : ℕ} (hi : i < MachineM.Nd d) :
    BG.zeta (BG.a1 τ') d m i = BG.zeta (BG.a1 τ) d (m + q1 τ τ' a d) i + a.1 :=
  zeta_shift hs.fcol (frameOffsets_phase _) (frameOffsets_phase _) hd m hi

theorem PShift.zeta2 {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {i : ℕ} (hi : i < MachineM.Nd d) :
    BG.zeta (BG.a2 τ') d m i = BG.zeta (BG.a2 τ) d (m + q2 τ τ' a d) i + a.2 :=
  zeta_shift hs.frow (frameOffsets_phase _) (frameOffsets_phase _) hd m hi

theorem PShift.prank1 (z : ℤ) : prankOf (col τ') z = prankOf (col τ) (z - a.1) :=
  prankOf_shift (fun l => (hs l).1) z

theorem PShift.prank2 (z : ℤ) : prankOf (row τ') z = prankOf (row τ) (z - a.2) :=
  prankOf_shift (fun l => (hs l).2) z

theorem PShift.cutH_eq {d : ℕ} (hd : 1 ≤ d) (m : ℤ) (cut : ℕ) {j : ℕ} (hj : j < Nd d) :
    cutH (row τ') d m cut j = cutH (row τ) d (m + q2 τ τ' a d) cut j := by
  rw [cutH, cutH, ite_eq_left hj, ite_eq_left hj, freeAt_eq_zeta (row τ') hd m hj,
    freeAt_eq_zeta (row τ) hd _ hj]
  show decide (prankOf (row τ') (BG.zeta (BG.a2 τ') d m j) < cut) = _
  rw [hs.zeta2 hd m hj, hs.prank2, add_sub_cancel_right]

theorem PShift.cutPi_eq {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {j : ℕ} (hj : j < Nd d) :
    cutPi (row τ') d m j = cutPi (row τ) d (m + q2 τ τ' a d) j := by
  rw [cutPi, cutPi, freeAt_eq_zeta (row τ') hd m hj, freeAt_eq_zeta (row τ) hd _ hj]
  show decide (prankOf (row τ') (BG.zeta (BG.a2 τ') d m j) % 2 = 1) = _
  rw [hs.zeta2 hd m hj, hs.prank2, add_sub_cancel_right]

end PShift

/-- The board run reads its input tracks only on the board. -/
theorem runP_congr {U : Machine} {n0 N : ℕ} {h pi h' pi' : ℕ → Bool}
    (hh : ∀ j < N, h j = h' j) (hp : ∀ j < N, pi j = pi' j) (i : ℕ) :
    MachineP.runP U n0 N h pi i = MachineP.runP U n0 N h' pi' i := by
  simp only [MachineP.runP]
  congr 1
  funext j
  rw [hh j j.2, hp j j.2]

theorem PShift.sAt_eq {τ τ' : ℕ → Bool × Bool} {a : Plane} (hs : PShift τ τ' a) {U : Machine}
    {n0 cut d : ℕ} (hd : 1 ≤ d) (m : ℤ) (i j : ℕ) :
    sAt U n0 cut τ' d m i j = sAt U n0 cut τ d (m + q2 τ τ' a d) i j := by
  by_cases hj : j < Nd d
  · rw [sAt_of hj, sAt_of hj]
    exact congrFun (runP_congr (fun j' hj' => hs.cutH_eq hd m cut hj')
      (fun j' hj' => hs.cutPi_eq hd m hj') i) ⟨j, hj⟩
  · rw [sAt, sAt, dite_eq_right hj, dite_eq_right hj]


/-! ## Nearest walls and tags along a translated line -/

section Tags

variable {S : Type} (W : ℤ → Option S) (c : ℤ)

theorem wdL_shift (z : ℤ) : BG.wdL (fun x => W (x - c)) z = BG.wdL W (z - c) := by
  classical
  by_cases h : ∃ n : ℕ, W (z - c - n) ≠ none
  · obtain ⟨h1, h2⟩ := BG.wdL_spec h
    refine BG.wdL_eq ?_ ?_
    · show W (z - _ - c) ≠ none
      rwa [sub_right_comm]
    · intro k hk
      show W (z - k - c) = none
      rw [sub_right_comm]
      exact h2 k hk
  · have h' : ¬ ∃ n : ℕ, (fun x => W (x - c)) (z - n) ≠ none := by
      rintro ⟨n, hn⟩
      have hn' : W (z - n - c) ≠ none := hn
      exact h ⟨n, by rwa [sub_right_comm] at hn'⟩
    rw [BG.wdL, dite_eq_right h', BG.wdL, dite_eq_right h]

theorem wdR_shift (z : ℤ) : BG.wdR (fun x => W (x - c)) z = BG.wdR W (z - c) := by
  classical
  have e : ∀ n : ℤ, z + 1 + n - c = z - c + 1 + n := fun n => by ring
  by_cases h : ∃ n : ℕ, W (z - c + 1 + n) ≠ none
  · obtain ⟨h1, h2⟩ := BG.wdR_spec h
    refine BG.wdR_eq ?_ ?_
    · show W (z + 1 + _ - c) ≠ none
      rwa [e]
    · intro k hk
      show W (z + 1 + k - c) = none
      rw [e]
      exact h2 k hk
  · have h' : ¬ ∃ n : ℕ, (fun x => W (x - c)) (z + 1 + n) ≠ none := by
      rintro ⟨n, hn⟩
      have hn' : W (z + 1 + n - c) ≠ none := hn
      exact h ⟨n, by rwa [e] at hn'⟩
    rw [BG.wdR, dite_eq_right h', BG.wdR, dite_eq_right h]

theorem wtag_shift (dflt : S) (z : ℤ) :
    BG.wtag (fun x => W (x - c)) dflt z = BG.wtag W dflt (z - c) := by
  simp only [BG.wtag, wdL_shift, wdR_shift]
  rw [sub_right_comm z, show z + 1 + (BG.wdR W (z - c) : ℤ) - c = z - c + 1 + BG.wdR W (z - c) by
    ring]

theorem evTag_shift (L R : S) (act : ℤ → Prop) (z : ℤ) :
    BG.evTag (fun x => W (x - c)) L R (fun x => act (x - c)) z = BG.evTag W L R act (z - c) := by
  classical
  have e1 : (∃ x, z - (BG.wdL W (z - c) : ℤ) < x ∧ x ≤ z ∧ act (x - c)) ↔
      (∃ x, z - c - (BG.wdL W (z - c) : ℤ) < x ∧ x ≤ z - c ∧ act x) :=
    ⟨fun ⟨x, h1, h2, h3⟩ => ⟨x - c, by omega, by omega, h3⟩,
      fun ⟨x, h1, h2, h3⟩ => ⟨x + c, by omega, by omega, by rwa [add_sub_cancel_right]⟩⟩
  have e2 : (∃ x, z < x ∧ x < z + 1 + (BG.wdR W (z - c) : ℤ) ∧ act (x - c)) ↔
      (∃ x, z - c < x ∧ x < z - c + 1 + (BG.wdR W (z - c) : ℤ) ∧ act x) :=
    ⟨fun ⟨x, h1, h2, h3⟩ => ⟨x - c, by omega, by omega, h3⟩,
      fun ⟨x, h1, h2, h3⟩ => ⟨x + c, by omega, by omega, by rwa [add_sub_cancel_right]⟩⟩
  unfold BG.evTag
  rw [wtag_shift, wdL_shift, wdR_shift]
  by_cases h : BG.wtag W L (z - c) = (L, R)
  · rw [ite_eq_left h, ite_eq_left h]
    simp only [Option.some.injEq, Prod.mk.injEq]
    exact ⟨if_congr e1 rfl rfl, if_congr e2 rfl rfl⟩
  · rw [ite_eq_right h, ite_eq_right h]

end Tags

/-! ## The construction of a translated phase is the translated construction -/

/-- `τ'` is the translate `τ + a` of `τ`, both resolving, so `Y_{τ'} = T_a Y_τ`. -/
structure PTrans (τ τ' : ℕ → Bool × Bool) (a : Plane) : Prop where
  ps : PShift τ τ' a
  q : ∀ ξ, qtilingOf τ' ξ = qtilingOf τ (ξ - a)

/-- `Y_{τ+a} = T_a Y_τ` for resolving `τ` and `τ + a` (`prop:quarter-ti`(a), as in the hard-model
core's `PhaseSystem.shift_Ψ`). -/
theorem ptrans_addDig {τ : ℕ → Bool × Bool} {a : Plane} (h1 : QResolving τ)
    (h2 : QResolving (addDig a τ)) : PTrans τ (addDig a τ) a :=
  ⟨pshift_addDig a τ, fun ξ => (congrFun (quarterSystem.shift_Ψ (υ := τ) h1 a h2) ξ).symm⟩

namespace PTrans

variable {τ τ' : ℕ → Bool × Bool} {a : Plane} (ht : PTrans τ τ' a)
include ht

theorem rowW (y : ℤ) : BG.rowW τ' y = fun z => BG.rowW τ (y - a.2) (z - a.1) := by
  funext z
  show (qtilingOf τ' (z, y)).VW = (qtilingOf τ (z - a.1, y - a.2)).VW
  rw [ht.q]
  rfl

theorem colW (x : ℤ) : BG.colW τ' x = fun z => BG.colW τ (x - a.1) (z - a.2) := by
  funext z
  show (qtilingOf τ' (x, z)).HW = (qtilingOf τ (x - a.1, z - a.2)).HW
  rw [ht.q]
  rfl

theorem oEc (ξ : Plane) : BG.oEc τ' ξ = BG.oEc τ (ξ - a) := by
  show BG.wtag (BG.rowW τ' ξ.2) .L ξ.1 = BG.wtag (BG.rowW τ (ξ.2 - a.2)) .L (ξ.1 - a.1)
  rw [ht.rowW, wtag_shift]

theorem oNc (ξ : Plane) : BG.oNc τ' ξ = BG.oNc τ (ξ - a) := by
  show BG.wtag (BG.colW τ' ξ.1) .B ξ.2 = BG.wtag (BG.colW τ (ξ.1 - a.1)) .B (ξ.2 - a.2)
  rw [ht.colW, wtag_shift]

theorem actF (ξ : Plane) : BG.actF τ' ξ ↔ BG.actF τ (ξ - a) := by
  constructor
  · rintro ⟨d, m1, m2, hd, h1, h2⟩
    exact ⟨d, m1 + q1 τ τ' a d, m2 + q2 τ τ' a d, hd, (isFree_shift ht.ps.fcol d m1 _).1 h1,
      (isFree_shift ht.ps.frow d m2 _).1 h2⟩
  · rintro ⟨d, m1, m2, hd, h1, h2⟩
    refine ⟨d, m1 - q1 τ τ' a d, m2 - q2 τ τ' a d, hd, (isFree_shift ht.ps.fcol d _ _).2 ?_,
      (isFree_shift ht.ps.frow d _ _).2 ?_⟩
    · rw [sub_add_cancel]; exact h1
    · rw [sub_add_cancel]; exact h2

theorem eEc (ξ : Plane) : BG.eEc τ' ξ = BG.eEc τ (ξ - a) := by
  show BG.evTag (BG.rowW τ' ξ.2) .L .R (fun x => BG.actF τ' (x, ξ.2)) ξ.1 =
    BG.evTag (BG.rowW τ (ξ.2 - a.2)) .L .R (fun x => BG.actF τ (x, ξ.2 - a.2)) (ξ.1 - a.1)
  have e : (fun x => BG.actF τ' (x, ξ.2)) = fun x => BG.actF τ (x - a.1, ξ.2 - a.2) :=
    funext fun x => propext (ht.actF (x, ξ.2))
  rw [ht.rowW, e]
  exact evTag_shift (BG.rowW τ (ξ.2 - a.2)) a.1 .L .R (fun x => BG.actF τ (x, ξ.2 - a.2)) ξ.1

theorem eNc (ξ : Plane) : BG.eNc τ' ξ = BG.eNc τ (ξ - a) := by
  show BG.evTag (BG.colW τ' ξ.1) .B .T (fun z => BG.actF τ' (ξ.1, z)) ξ.2 =
    BG.evTag (BG.colW τ (ξ.1 - a.1)) .B .T (fun z => BG.actF τ (ξ.1 - a.1, z)) (ξ.2 - a.2)
  have e : (fun z => BG.actF τ' (ξ.1, z)) = fun z => BG.actF τ (ξ.1 - a.1, z - a.2) :=
    funext fun z => propext (ht.actF (ξ.1, z))
  rw [ht.colW, e]
  exact evTag_shift (BG.colW τ (ξ.1 - a.1)) a.2 .B .T (fun z => BG.actF τ (ξ.1 - a.1, z)) ξ.2

theorem dqOf (cut : ℕ) (ξ : Plane) : dqOf cut τ' ξ = dqOf cut τ (ξ - a) := by
  simp only [Chart.dqOf, ht.q ξ, ht.ps.prank1, ht.ps.prank2]
  rfl

theorem hseg {d i j : ℕ} {m : ℤ} {ξ : Plane} :
    HSegM τ' (d, i, j, m) ξ ↔ HSegM τ (d, i, j, m + q2 τ τ' a d) (ξ - a) := by
  constructor
  · rintro ⟨hd, hi, hj, m1, e, l1, l2⟩
    dsimp only at hd hi hj e l1 l2
    rw [ht.ps.zeta2 hd m hj] at e
    rw [ht.ps.zeta1 hd m1 (by omega)] at l1
    rw [ht.ps.zeta1 hd m1 hi] at l2
    refine ⟨hd, hi, hj, m1 + q1 τ τ' a d, ?_, ?_, ?_⟩
    · show ξ.2 - a.2 = BG.zeta (BG.a2 τ) d (m + q2 τ τ' a d) j; omega
    · show BG.zeta (BG.a1 τ) d (m1 + q1 τ τ' a d) i ≤ ξ.1 - a.1; omega
    · show ξ.1 - a.1 < BG.zeta (BG.a1 τ) d (m1 + q1 τ τ' a d) (i + 1); omega
  · rintro ⟨hd, hi, hj, m1, e, l1, l2⟩
    dsimp only at hd hi hj e l1 l2
    refine ⟨hd, hi, hj, m1 - q1 τ τ' a d, ?_, ?_, ?_⟩
    · show ξ.2 = BG.zeta (BG.a2 τ') d m j
      rw [ht.ps.zeta2 hd m hj]
      change ξ.2 - a.2 = _ at e
      omega
    · show BG.zeta (BG.a1 τ') d (m1 - q1 τ τ' a d) i ≤ ξ.1
      rw [ht.ps.zeta1 hd _ (by omega), sub_add_cancel]
      change _ ≤ ξ.1 - a.1 at l1
      omega
    · show ξ.1 < BG.zeta (BG.a1 τ') d (m1 - q1 τ τ' a d) (i + 1)
      rw [ht.ps.zeta1 hd _ hi, sub_add_cancel]
      change ξ.1 - a.1 < _ at l2
      omega

theorem vseg {d i j : ℕ} {m : ℤ} {ξ : Plane} :
    VSegM τ' (d, i, j, m) ξ ↔ VSegM τ (d, i, j, m + q2 τ τ' a d) (ξ - a) := by
  constructor
  · rintro ⟨hd, hi, hj, m1, e, l1, l2⟩
    dsimp only at hd hi hj e l1 l2
    rw [ht.ps.zeta1 hd m1 hi] at e
    rw [ht.ps.zeta2 hd m (by omega)] at l1
    rw [ht.ps.zeta2 hd m hj] at l2
    refine ⟨hd, hi, hj, m1 + q1 τ τ' a d, ?_, ?_, ?_⟩
    · show ξ.1 - a.1 = BG.zeta (BG.a1 τ) d (m1 + q1 τ τ' a d) i; omega
    · show BG.zeta (BG.a2 τ) d (m + q2 τ τ' a d) j ≤ ξ.2 - a.2; omega
    · show ξ.2 - a.2 < BG.zeta (BG.a2 τ) d (m + q2 τ τ' a d) (j + 1); omega
  · rintro ⟨hd, hi, hj, m1, e, l1, l2⟩
    dsimp only at hd hi hj e l1 l2
    refine ⟨hd, hi, hj, m1 - q1 τ τ' a d, ?_, ?_, ?_⟩
    · show ξ.1 = BG.zeta (BG.a1 τ') d (m1 - q1 τ τ' a d) i
      rw [ht.ps.zeta1 hd _ hi, sub_add_cancel]
      change ξ.1 - a.1 = _ at e
      omega
    · show BG.zeta (BG.a2 τ') d m j ≤ ξ.2
      rw [ht.ps.zeta2 hd m (by omega)]
      change _ ≤ ξ.2 - a.2 at l1
      omega
    · show ξ.2 < BG.zeta (BG.a2 τ') d m (j + 1)
      rw [ht.ps.zeta2 hd m hj]
      change ξ.2 - a.2 < _ at l2
      omega

theorem gsite {d : ℕ} (hd : 1 ≤ d) (m1 m : ℤ) {i j : ℕ} (hi : i < MachineM.Nd d)
    (hj : j < MachineM.Nd d) :
    BG.gsite τ' d m1 m i j = BG.gsite τ d (m1 + q1 τ τ' a d) (m + q2 τ τ' a d) i j + a := by
  simp only [BG.gsite, ht.ps.zeta1 hd m1 hi, ht.ps.zeta2 hd m hj]
  rfl

theorem gpos {d i j : ℕ} {m : ℤ} {ξ : Plane} :
    GPosM τ' (d, i, j, m) ξ ↔ GPosM τ (d, i, j, m + q2 τ τ' a d) (ξ - a) := by
  constructor
  · rintro ⟨hd, hi, hj, m1, e⟩
    dsimp only at hd hi hj e
    refine ⟨hd, hi, hj, m1 + q1 τ τ' a d, ?_⟩
    show ξ - a = BG.gsite τ d (m1 + q1 τ τ' a d) (m + q2 τ τ' a d) i j
    rw [e, ht.gsite hd m1 m hi hj, add_sub_cancel_right]
  · rintro ⟨hd, hi, hj, m1, e⟩
    dsimp only at hd hi hj e
    refine ⟨hd, hi, hj, m1 - q1 τ τ' a d, ?_⟩
    show ξ = BG.gsite τ' d (m1 - q1 τ τ' a d) m i j
    rw [ht.gsite hd _ m hi hj, sub_add_cancel, ← e, sub_add_cancel]

variable {U : Machine} {n0 cut : ℕ}

theorem lEm (ξ : Plane) : lEm U n0 cut τ' ξ = lEm U n0 cut τ (ξ - a) := by
  by_cases h : ∃ p, HSegM τ' p ξ
  · obtain ⟨⟨d, i, j, m⟩, hp⟩ := h
    rw [lEm_of hp, lEm_of (ht.hseg.1 hp)]
    exact congrArg some (ht.ps.sAt_eq hp.1 m (i + 1) j)
  · rw [lEm_none h, lEm_none]
    rintro ⟨⟨d, i, j, m⟩, hp⟩
    refine h ⟨(d, i, j, m - q2 τ τ' a d), ht.hseg.2 ?_⟩
    rwa [sub_add_cancel]

theorem lNm (ξ : Plane) : lNm U n0 cut τ' ξ = lNm U n0 cut τ (ξ - a) := by
  by_cases h : ∃ p, VSegM τ' p ξ
  · obtain ⟨⟨d, i, j, m⟩, hp⟩ := h
    rw [lNm_of hp, lNm_of (ht.vseg.1 hp)]
    exact congrArg some (Prod.ext (ht.ps.sAt_eq hp.1 m i j) (ht.ps.sAt_eq hp.1 m i (j + 1)))
  · rw [lNm_none h, lNm_none]
    rintro ⟨⟨d, i, j, m⟩, hp⟩
    refine h ⟨(d, i, j, m - q2 τ τ' a d), ht.vseg.2 ?_⟩
    rwa [sub_add_cancel]

theorem kFm (ξ : Plane) : kFm U n0 cut τ' ξ = kFm U n0 cut τ (ξ - a) := by
  by_cases h : ∃ p, GPosM τ' p ξ
  · obtain ⟨⟨d, i, j, m⟩, hp⟩ := h
    rw [kFm_of hp, kFm_of (ht.gpos.1 hp)]
    have hd : 1 ≤ d := hp.1
    simp only [recF, ht.ps.sAt_eq hd m]
  · rw [kFm_none h, kFm_none]
    rintro ⟨⟨d, i, j, m⟩, hp⟩
    refine h ⟨(d, i, j, m - q2 τ τ' a d), ht.gpos.2 ?_⟩
    rwa [sub_add_cancel]

theorem rawVal (ξ : Plane) : rawVal U n0 cut τ' ξ = rawVal U n0 cut τ (ξ - a) := by
  have p1 : ((ξ.1 - 1, ξ.2) : Plane) - a = ((ξ - a).1 - 1, (ξ - a).2) :=
    Prod.ext (by simp only [Prod.fst_sub]; ring) rfl
  have p2 : ((ξ.1, ξ.2 - 1) : Plane) - a = ((ξ - a).1, (ξ - a).2 - 1) :=
    Prod.ext rfl (by simp only [Prod.snd_sub]; ring)
  simp only [Chart.rawVal, ht.dqOf, ht.oEc, ht.oNc, ht.eEc, ht.eNc, ht.lEm, ht.lNm, ht.kFm, p1,
    p2]

theorem wordAt (ρ : ℕ) (ξ : Plane) :
    wordAt ρ (qtilingOf τ') ξ = wordAt ρ (qtilingOf τ) (ξ - a) := by
  funext w
  simp only [Chart.wordAt, ht.q]
  congr 1
  abel

theorem rawOf {k : ℕ} (ξ : Plane) : rawOf U n0 k cut τ' ξ = rawOf U n0 k cut τ (ξ - a) :=
  Prod.ext (ht.rawVal ξ) (ht.wordAt _ ξ)

theorem chartOf {k : ℕ} (t0 : RTile (contentP U n0) k) (ξ : Plane) :
    chartOf U n0 k cut τ' t0 ξ = chartOf U n0 k cut τ t0 (ξ - a) :=
  congrArg (toTile U n0 k t0) (ht.rawOf ξ)

end PTrans

/-- **The chart of `τ + a` is the translate of the chart of `τ`** (`τ`, `τ + a` resolving). -/
theorem chartOf_shift {U : Machine} {n0 k cut : ℕ} {τ : ℕ → Bool × Bool} {a : Plane}
    (h1 : QResolving τ) (h2 : QResolving (addDig a τ)) (t0 : RTile (contentP U n0) k) :
    chartOf U n0 k cut (addDig a τ) t0 = UPD.shift a (chartOf U n0 k cut τ t0) :=
  funext fun ξ => (ptrans_addDig h1 h2).chartOf t0 ξ


/-! ## Typical phases: measurable, of full Haar measure (D31) -/

theorem measurableSet_dig_col (m : ℕ) (z : ℤ) (b : Bool) :
    MeasurableSet {τ : ℕ → Bool × Bool | dig (col τ) m z = b} :=
  BG.measurableSet_prefix (m + 1) _ fun x y h hx => by
    rw [← hx]
    exact dig_congr (fun i hi => by show (y i).1 = (x i).1; rw [h i (by omega)]) z

theorem measurableSet_dig_row (m : ℕ) (z : ℤ) (b : Bool) :
    MeasurableSet {τ : ℕ → Bool × Bool | dig (row τ) m z = b} :=
  BG.measurableSet_prefix (m + 1) _ fun x y h hx => by
    rw [← hx]
    exact dig_congr (fun i hi => by show (y i).2 = (x i).2; rw [h i (by omega)]) z

theorem measurableSet_digP (x : Plane) (m : ℕ) (p : Bool × Bool) :
    MeasurableSet {υ : ℕ → Bool × Bool | digP υ x m = p} := by
  have e : {υ : ℕ → Bool × Bool | digP υ x m = p} =
      {υ | dig (col υ) m x.1 = p.1} ∩ {υ | dig (row υ) m x.2 = p.2} := by
    ext υ
    simp only [digP, Set.mem_ofPred_eq, Set.mem_inter_iff, Prod.ext_iff]
  rw [e]
  exact (measurableSet_dig_col _ _ _).inter (measurableSet_dig_row _ _ _)

theorem measurableSet_resolving : MeasurableSet {υ : ℕ → Bool × Bool | Resolving υ} := by
  have e : {υ : ℕ → Bool × Bool | Resolving υ} = ⋂ x : Plane, ⋃ m : ℕ,
      {υ | digP υ x m = (true, true)} ∩ {υ | digP υ x (m + 1) = (true, true)} := by
    ext υ
    simp only [Resolving, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff]
  rw [e]
  exact MeasurableSet.iInter fun x => MeasurableSet.iUnion fun m =>
    (measurableSet_digP _ _ _).inter (measurableSet_digP _ _ _)

/-- **The typical phases form a measurable set** (D31). -/
theorem measurableSet_typical : MeasurableSet {τ : ℕ → Bool × Bool | Typical τ} := by
  have hQ : MeasurableSet {τ : ℕ → Bool × Bool | QResolving τ} :=
    measurable_tail measurableSet_resolving
  have hN1 : MeasurableSet {τ : ℕ → Bool × Bool | NotInt (col τ)} := by
    have e : {τ : ℕ → Bool × Bool | NotInt (col τ)} =
        ⋂ z : ℤ, ⋃ m : ℕ, {τ | dig (col τ) m z = true} := by
      ext τ; simp only [NotInt, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
    rw [e]
    exact MeasurableSet.iInter fun z => MeasurableSet.iUnion fun m => measurableSet_dig_col m z true
  have hN2 : MeasurableSet {τ : ℕ → Bool × Bool | NotInt (row τ)} := by
    have e : {τ : ℕ → Bool × Bool | NotInt (row τ)} =
        ⋂ z : ℤ, ⋃ m : ℕ, {τ | dig (row τ) m z = true} := by
      ext τ; simp only [NotInt, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion]
    rw [e]
    exact MeasurableSet.iInter fun z => MeasurableSet.iUnion fun m => measurableSet_dig_row m z true
  have hD1 : MeasurableSet {τ : ℕ → Bool × Bool | ∀ z : ℤ, ∃ d, 1 ≤ d ∧ Digit2 (col τ) z d} := by
    have e : {τ : ℕ → Bool × Bool | ∀ z : ℤ, ∃ d, 1 ≤ d ∧ Digit2 (col τ) z d} =
        ⋂ z : ℤ, ⋃ d : ℕ, {_τ : ℕ → Bool × Bool | 1 ≤ d} ∩
          ({τ | dig (col τ) (2 * d) z = false} ∩ {τ | dig (col τ) (2 * d + 1) z = true}) := by
      ext τ
      simp only [Digit2, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff]
    rw [e]
    exact MeasurableSet.iInter fun z => MeasurableSet.iUnion fun d =>
      (MeasurableSet.const _).inter ((measurableSet_dig_col _ z false).inter
        (measurableSet_dig_col _ z true))
  have hD2 : MeasurableSet {τ : ℕ → Bool × Bool | ∀ z : ℤ, ∃ d, 1 ≤ d ∧ Digit2 (row τ) z d} := by
    have e : {τ : ℕ → Bool × Bool | ∀ z : ℤ, ∃ d, 1 ≤ d ∧ Digit2 (row τ) z d} =
        ⋂ z : ℤ, ⋃ d : ℕ, {_τ : ℕ → Bool × Bool | 1 ≤ d} ∩
          ({τ | dig (row τ) (2 * d) z = false} ∩ {τ | dig (row τ) (2 * d + 1) z = true}) := by
      ext τ
      simp only [Digit2, Set.mem_ofPred_eq, Set.mem_iInter, Set.mem_iUnion, Set.mem_inter_iff]
    rw [e]
    exact MeasurableSet.iInter fun z => MeasurableSet.iUnion fun d =>
      (MeasurableSet.const _).inter ((measurableSet_dig_row _ z false).inter
        (measurableSet_dig_row _ z true))
  exact hQ.inter (hN1.inter (hN2.inter (hD1.inter hD2)))

/-- **The typical phases have full Haar measure** (D31; `UPD.Scaffold.ae_typical`). -/
theorem haar_typical : haar {τ : ℕ → Bool × Bool | Typical τ} = 1 := by
  rw [← prob_compl_eq_zero_iff measurableSet_typical]
  exact ae_iff.1 ae_typical

/-! ## Measurability of `τ ↦` the chart -/

section Measurable

theorem mlevel_pi {Ω ι α : Type} [MeasurableSpace Ω] [Countable ι] {f : Ω → ι → α}
    (h : ∀ i, BG.MLevel (fun ω => f ω i)) : BG.MLevel f := fun v => by
  have e : {ω | f ω = v} = ⋂ i, {ω | f ω i = v i} := by
    ext ω; simp only [Set.mem_ofPred_eq, Set.mem_iInter, funext_iff]
  rw [e]
  exact MeasurableSet.iInter fun i => h i (v i)

/-- A choice-defined field is measurable when its defining predicate has measurable level sets and
determines the witness, and the value at each witness is measurable. -/
theorem mlevel_choose' {κ α : Type} [Countable κ] {P : (ℕ → Bool × Bool) → κ → Prop}
    (hP : ∀ p, MeasurableSet {τ | P τ p}) (F : κ → (ℕ → Bool × Bool) → α)
    (hF : ∀ p, BG.MLevel (F p)) (dflt : α) {f : (ℕ → Bool × Bool) → α}
    (hf : ∀ τ, (∀ p, P τ p → f τ = F p τ) ∧ ((¬ ∃ p, P τ p) → f τ = dflt)) : BG.MLevel f := by
  intro v
  have e : {τ | f τ = v} = (⋃ p, {τ | P τ p} ∩ {τ | F p τ = v}) ∪
      ({τ | ∃ p, P τ p}ᶜ ∩ {_τ | dflt = v}) := by
    ext τ
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_compl_iff]
    constructor
    · intro h
      by_cases hex : ∃ p, P τ p
      · obtain ⟨p, hp⟩ := hex; exact Or.inl ⟨p, hp, by rw [← (hf τ).1 p hp, h]⟩
      · exact Or.inr ⟨hex, by rw [← (hf τ).2 hex, h]⟩
    · rintro (⟨p, hp, hFp⟩ | ⟨hex, hd⟩)
      · rw [(hf τ).1 p hp, hFp]
      · rw [(hf τ).2 hex, hd]
  have hex : MeasurableSet {τ | ∃ p, P τ p} := by
    have e' : {τ | ∃ p, P τ p} = ⋃ p, {τ | P τ p} := by ext; simp
    rw [e']; exact MeasurableSet.iUnion hP
  rw [e]
  exact (MeasurableSet.iUnion fun p => (hP p).inter (hF p v)).union
    (hex.compl.inter (MeasurableSet.const _))

theorem mlevel_prankOf_col (z : ℤ) :
    BG.MLevel (fun τ : ℕ → Bool × Bool => prankOf (col τ) z) := by
  classical
  have hP : ∀ r, MeasurableSet {τ : ℕ → Bool × Bool | PRank (col τ) z r} := fun r => by
    have e : {τ : ℕ → Bool × Bool | PRank (col τ) z r} =
        {τ | dig (col τ) (r + 1) z = true} ∩ ⋂ m : Fin r, {τ | dig (col τ) (m.1 + 1) z = false} := by
      ext τ
      simp only [prank_iff_dig, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      exact and_congr_right fun _ => ⟨fun h m => h m.1 m.2, fun h m hm => h ⟨m, hm⟩⟩
    rw [e]
    exact (measurableSet_dig_col _ _ _).inter (MeasurableSet.iInter fun m => measurableSet_dig_col _ _ _)
  refine mlevel_choose' (κ := ℕ) hP (fun r _ => r) (fun r => BG.MLevel.const r) 0 fun τ =>
    ⟨fun r hr => prankOf_eq hr, fun hex => by unfold prankOf; rw [dite_eq_right hex]⟩

theorem mlevel_prankOf_row (z : ℤ) :
    BG.MLevel (fun τ : ℕ → Bool × Bool => prankOf (row τ) z) := by
  classical
  have hP : ∀ r, MeasurableSet {τ : ℕ → Bool × Bool | PRank (row τ) z r} := fun r => by
    have e : {τ : ℕ → Bool × Bool | PRank (row τ) z r} =
        {τ | dig (row τ) (r + 1) z = true} ∩ ⋂ m : Fin r, {τ | dig (row τ) (m.1 + 1) z = false} := by
      ext τ
      simp only [prank_iff_dig, Set.mem_ofPred_eq, Set.mem_inter_iff, Set.mem_iInter]
      exact and_congr_right fun _ => ⟨fun h m => h m.1 m.2, fun h m hm => h ⟨m, hm⟩⟩
    rw [e]
    exact (measurableSet_dig_row _ _ _).inter (MeasurableSet.iInter fun m => measurableSet_dig_row _ _ _)
  refine mlevel_choose' (κ := ℕ) hP (fun r _ => r) (fun r => BG.MLevel.const r) 0 fun τ =>
    ⟨fun r hr => prankOf_eq hr, fun hex => by unfold prankOf; rw [dite_eq_right hex]⟩

theorem mlevel_dqOf (cut : ℕ) (ξ : Plane) : BG.MLevel (fun τ => dqOf cut τ ξ) :=
  ((BG.mlevel_qtiling ξ).prod ((mlevel_prankOf_col ξ.1).prod (mlevel_prankOf_row ξ.2))).comp
    fun x : Quarter × ℕ × ℕ => (⟨x.1.quad, ⟨⟨x.1.parent,
      (okBits x.1.parent.1.base.black (decide (x.2.1 < cut)) (decide (x.2.2 < cut))).1,
      (okBits x.1.parent.1.base.black (decide (x.2.1 < cut)) (decide (x.2.2 < cut))).2⟩,
      rankOK_okBits _ _ _⟩⟩ : DQuarter)

theorem freeAt_congr {t t' : ℕ → Bool} {d : ℕ}
    (h : ∀ e ≤ d, phaseOffsets t e = phaseOffsets t' e) (m : ℤ) (j : ℕ) :
    freeAt t d m j = freeAt t' d m j := by
  have hr := BG.rfree_congr (h d le_rfl) m
  have hF : FreeOff t d m = FreeOff t' d m := by
    funext n
    simp only [FreeOff, hr]
    exact propext (BG.isFree_congr h m _)
  simp only [freeAt, hF, hr]

theorem mlevel_freeAt_row (d : ℕ) (m : ℤ) (j : ℕ) :
    BG.MLevel (fun τ : ℕ → Bool × Bool => freeAt (row τ) d m j) := fun v =>
  BG.measurableSet_prefix (2 * d + 2) _ fun x y h hx => by
    rw [← hx]
    exact freeAt_congr (fun e he => (BG.a2_congr h he).symm) m j

theorem mlevel_cutH (d : ℕ) (m : ℤ) (cut j : ℕ) :
    BG.MLevel (fun τ : ℕ → Bool × Bool => cutH (row τ) d m cut j) := by
  have h := BG.MLevel.dep (mlevel_freeAt_row d m j) (F := fun z τ => prankOf (row τ) z)
    fun z => mlevel_prankOf_row z
  by_cases hj : j < Nd d
  · have e : (fun τ : ℕ → Bool × Bool => cutH (row τ) d m cut j) =
        fun τ => decide (prankOf (row τ) (freeAt (row τ) d m j) < cut) :=
      funext fun τ => by rw [cutH, ite_eq_left hj]
    rw [e]
    exact h.comp fun r => decide (r < cut)
  · have e : (fun τ : ℕ → Bool × Bool => cutH (row τ) d m cut j) = fun _ => true :=
      funext fun τ => by rw [cutH, ite_eq_right hj]
    rw [e]
    exact BG.MLevel.const true

theorem mlevel_cutPi (d : ℕ) (m : ℤ) (j : ℕ) :
    BG.MLevel (fun τ : ℕ → Bool × Bool => cutPi (row τ) d m j) :=
  (BG.MLevel.dep (mlevel_freeAt_row d m j) (F := fun z τ => prankOf (row τ) z)
    fun z => mlevel_prankOf_row z).comp fun r => decide (r % 2 = 1)

variable (U : Machine) (n0 k cut : ℕ)

theorem mlevel_sAt (d : ℕ) (m : ℤ) (i j : ℕ) :
    BG.MLevel (fun τ => sAt U n0 cut τ d m i j) := by
  let G : (Fin (Nd d) → Bool × Bool) → MachineP.Cell U n0 := fun g =>
    if hj : j < Nd d then
      MachineP.runP U n0 (Nd d) (fun j' => if h : j' < Nd d then (g ⟨j', h⟩).1 else true)
        (fun j' => if h : j' < Nd d then (g ⟨j', h⟩).2 else false) i ⟨j, hj⟩
    else MachineP.initP U n0 false false false
  have hg := mlevel_pi (f := fun (τ : ℕ → Bool × Bool) (j' : Fin (Nd d)) =>
    (cutH (row τ) d m cut j', cutPi (row τ) d m j')) fun j' =>
      (mlevel_cutH d m cut j').prod (mlevel_cutPi d m j')
  have e : (fun τ => sAt U n0 cut τ d m i j) =
      fun τ => G (fun j' : Fin (Nd d) => (cutH (row τ) d m cut j', cutPi (row τ) d m j')) := by
    funext τ
    by_cases hj : j < Nd d
    · rw [sAt_of hj]
      simp only [G, dite_eq_left hj]
      exact congrFun (runP_congr (fun j' hj' => by rw [dite_eq_left hj'])
        (fun j' hj' => by rw [dite_eq_left hj']) i) ⟨j, hj⟩
    · simp only [sAt, G, dite_eq_right hj]
  rw [e]
  exact hg.comp G

theorem measurableSet_HSegM (p : ℕ × ℕ × ℕ × ℤ) (ξ : Plane) :
    MeasurableSet {τ | HSegM τ p ξ} := by
  have e : {τ | HSegM τ p ξ} = ⋃ m1 : ℤ, {τ | 1 ≤ p.1 ∧ p.2.1 + 1 < MachineM.Nd p.1 ∧
      p.2.2.1 < MachineM.Nd p.1 ∧ ξ.2 = BG.zeta (BG.a2 τ) p.1 p.2.2.2 p.2.2.1 ∧
      BG.zeta (BG.a1 τ) p.1 m1 p.2.1 ≤ ξ.1 ∧ ξ.1 < BG.zeta (BG.a1 τ) p.1 m1 (p.2.1 + 1)} := by
    ext τ; simp only [HSegM, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨h1, h2, h3, m1, h4⟩; exact ⟨m1, h1, h2, h3, h4⟩
    · rintro ⟨m1, h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, m1, h4⟩
  rw [e]
  refine MeasurableSet.iUnion fun m1 => BG.measurableSet_prefix (2 * p.1 + 2) _ fun x y h hx => ?_
  have z1 := BG.zeta_congr (fun e he => BG.a1_congr h he) m1
  have z2 := BG.zeta_congr (fun e he => BG.a2_congr h he) p.2.2.2
  rw [z1, z1, z2] at hx
  exact hx

theorem measurableSet_VSegM (p : ℕ × ℕ × ℕ × ℤ) (ξ : Plane) :
    MeasurableSet {τ | VSegM τ p ξ} := by
  have e : {τ | VSegM τ p ξ} = ⋃ m1 : ℤ, {τ | 1 ≤ p.1 ∧ p.2.1 < MachineM.Nd p.1 ∧
      p.2.2.1 + 1 < MachineM.Nd p.1 ∧ ξ.1 = BG.zeta (BG.a1 τ) p.1 m1 p.2.1 ∧
      BG.zeta (BG.a2 τ) p.1 p.2.2.2 p.2.2.1 ≤ ξ.2 ∧
      ξ.2 < BG.zeta (BG.a2 τ) p.1 p.2.2.2 (p.2.2.1 + 1)} := by
    ext τ; simp only [VSegM, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨h1, h2, h3, m1, h4⟩; exact ⟨m1, h1, h2, h3, h4⟩
    · rintro ⟨m1, h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, m1, h4⟩
  rw [e]
  refine MeasurableSet.iUnion fun m1 => BG.measurableSet_prefix (2 * p.1 + 2) _ fun x y h hx => ?_
  have z1 := BG.zeta_congr (fun e he => BG.a1_congr h he) m1
  have z2 := BG.zeta_congr (fun e he => BG.a2_congr h he) p.2.2.2
  rw [z1, z2, z2] at hx
  exact hx

theorem measurableSet_GPosM (p : ℕ × ℕ × ℕ × ℤ) (ξ : Plane) :
    MeasurableSet {τ | GPosM τ p ξ} := by
  have e : {τ | GPosM τ p ξ} = ⋃ m1 : ℤ, {τ | 1 ≤ p.1 ∧ p.2.1 < MachineM.Nd p.1 ∧
      p.2.2.1 < MachineM.Nd p.1 ∧ ξ = BG.gsite τ p.1 m1 p.2.2.2 p.2.1 p.2.2.1} := by
    ext τ; simp only [GPosM, Set.mem_ofPred_eq, Set.mem_iUnion]
    constructor
    · rintro ⟨h1, h2, h3, m1, h4⟩; exact ⟨m1, h1, h2, h3, h4⟩
    · rintro ⟨m1, h1, h2, h3, h4⟩; exact ⟨h1, h2, h3, m1, h4⟩
  rw [e]
  refine MeasurableSet.iUnion fun m1 => BG.measurableSet_prefix (2 * p.1 + 2) _ fun x y h hx => ?_
  have z1 := BG.zeta_congr (fun e he => BG.a1_congr h he) m1
  have z2 := BG.zeta_congr (fun e he => BG.a2_congr h he) p.2.2.2
  simp only [BG.gsite] at hx ⊢
  rw [z1, z2] at hx
  exact hx

theorem mlevel_lEm (ξ : Plane) : BG.MLevel (fun τ => lEm U n0 cut τ ξ) :=
  mlevel_choose' (fun p => measurableSet_HSegM p ξ) (fun p τ => some (hcolF U n0 cut τ p))
    (fun _ => (mlevel_sAt U n0 cut _ _ _ _).comp some) none
    fun _ => ⟨fun _ hp => lEm_of hp, fun h => lEm_none h⟩

theorem mlevel_lNm (ξ : Plane) : BG.MLevel (fun τ => lNm U n0 cut τ ξ) :=
  mlevel_choose' (fun p => measurableSet_VSegM p ξ) (fun p τ => some (vcolF U n0 cut τ p))
    (fun _ => ((mlevel_sAt U n0 cut _ _ _ _).prod (mlevel_sAt U n0 cut _ _ _ _)).comp some) none
    fun _ => ⟨fun _ hp => lNm_of hp, fun h => lNm_none h⟩

theorem mlevel_kFm (ξ : Plane) : BG.MLevel (fun τ => kFm U n0 cut τ ξ) :=
  mlevel_choose' (fun p => measurableSet_GPosM p ξ) (fun p τ => some (recF U n0 cut τ p))
    (fun p => ((mlevel_sAt U n0 cut _ _ _ _).prod ((mlevel_sAt U n0 cut _ _ _ _).prod
      (mlevel_sAt U n0 cut _ _ _ _))).comp fun x => some
        (if p.2.2.1 = 0 then none else some x.1, x.2.1,
          if p.2.2.1 + 1 < Nd p.1 then some x.2.2 else none)) none
    fun _ => ⟨fun _ hp => kFm_of hp, fun h => kFm_none h⟩

theorem mlevel_rawVal (ξ : Plane) : BG.MLevel (fun τ => rawVal U n0 cut τ ξ) := by
  intro v
  obtain ⟨q, oW, oE, oS, oN, eW, eE, eS, eN, lW, lE, lS, lN, kk⟩ := v
  have e : {τ | rawVal U n0 cut τ ξ = ⟨q, oW, oE, oS, oN, eW, eE, eS, eN, lW, lE, lS, lN, kk⟩} =
      {τ | dqOf cut τ ξ = q} ∩ {τ | BG.oEc τ (ξ.1 - 1, ξ.2) = oW} ∩ {τ | BG.oEc τ ξ = oE} ∩
      {τ | BG.oNc τ (ξ.1, ξ.2 - 1) = oS} ∩ {τ | BG.oNc τ ξ = oN} ∩
      {τ | BG.eEc τ (ξ.1 - 1, ξ.2) = eW} ∩ {τ | BG.eEc τ ξ = eE} ∩
      {τ | BG.eNc τ (ξ.1, ξ.2 - 1) = eS} ∩ {τ | BG.eNc τ ξ = eN} ∩
      {τ | lEm U n0 cut τ (ξ.1 - 1, ξ.2) = lW} ∩ {τ | lEm U n0 cut τ ξ = lE} ∩
      {τ | lNm U n0 cut τ (ξ.1, ξ.2 - 1) = lS} ∩ {τ | lNm U n0 cut τ ξ = lN} ∩
      {τ | kFm U n0 cut τ ξ = kk} := by
    ext τ
    simp only [rawVal, RVal.mk.injEq, Set.mem_ofPred_eq, Set.mem_inter_iff, and_assoc]
  rw [e]
  exact (((((((((((((mlevel_dqOf cut ξ q).inter (BG.mlevel_oEc _ oW)).inter
    (BG.mlevel_oEc ξ oE)).inter (BG.mlevel_oNc _ oS)).inter (BG.mlevel_oNc ξ oN)).inter
    (BG.mlevel_eEc _ eW)).inter (BG.mlevel_eEc ξ eE)).inter (BG.mlevel_eNc _ eS)).inter
    (BG.mlevel_eNc ξ eN)).inter (mlevel_lEm U n0 cut _ lW)).inter (mlevel_lEm U n0 cut ξ lE)).inter
    (mlevel_lNm U n0 cut _ lS)).inter (mlevel_lNm U n0 cut ξ lN)).inter (mlevel_kFm U n0 cut ξ kk)

theorem mlevel_rawOf (ξ : Plane) : BG.MLevel (fun τ => rawOf U n0 k cut τ ξ) :=
  (mlevel_rawVal U n0 cut ξ).prod (mlevel_pi fun w => BG.mlevel_qtiling (ξ + w.1))

end Measurable

/-! ## The translation-invariant chart law -/

variable {S : Type} [Fintype S] [DecidableEq S]

instance (C : ContentOps S) (k : ℕ) : MeasurableSpace (RTile C k) := ⊤

instance (C : ContentOps S) (k : ℕ) : DiscreteMeasurableSpace (RTile C k) :=
  ⟨fun _ => MeasurableSpace.measurableSet_top⟩

section Law

variable {U : Machine} {n0 k cut : ℕ}

theorem measurable_chartOf (t0 : RTile (contentP U n0) k) :
    Measurable (fun τ => chartOf U n0 k cut τ t0) :=
  Measurable.of_eval fun ξ => measurable_to_countable' fun v =>
    (mlevel_rawOf U n0 k cut ξ).comp (toTile U n0 k t0) v

/-- The quarters of an `R`-chart. -/
def quartersOf (c : Plane → RTile (contentP U n0) k) : Plane → Quarter := fun ξ => (c ξ).1.1.q.toQ

theorem measurable_quartersOf : Measurable (quartersOf (U := U) (n0 := n0) (k := k)) :=
  Measurable.of_eval fun ξ =>
    (measurable_of_countable fun t : RTile (contentP U n0) k => t.1.1.q.toQ).comp
      (measurable_pi_apply ξ)

variable (U n0 k cut) in
/-- **The chart law** of Prop 4.3, nonhalting: the image of Haar measure under the map
`τ ↦` the computational chart of phase `τ`. -/
def chartLaw (t0 : RTile (contentP U n0) k) : Measure (Plane → RTile (contentP U n0) k) :=
  haar.map fun τ => chartOf U n0 k cut τ t0

theorem isProbabilityMeasure_chartLaw (t0 : RTile (contentP U n0) k) :
    IsProbabilityMeasure (chartLaw U n0 k cut t0) :=
  (Measure.isProbabilityMeasure_map_iff (measurable_chartOf t0).aemeasurable).2 inferInstance

/-- **The chart law is translation invariant.** -/
theorem chartLaw_shift (t0 : RTile (contentP U n0) k) (a : Plane) :
    (chartLaw U n0 k cut t0).map (UPD.shift a) = chartLaw U n0 k cut t0 := by
  unfold chartLaw
  rw [Measure.map_map (measurable_shift a) (measurable_chartOf t0)]
  have hae : (UPD.shift a ∘ fun τ => chartOf U n0 k cut τ t0) =ᵐ[haar]
      ((fun τ => chartOf U n0 k cut τ t0) ∘ addDig a) := by
    filter_upwards [BG.ae_typical_addDig a] with τ h
    exact (chartOf_shift h.1.1 h.2.1 t0).symm
  rw [Measure.map_congr hae, ← Measure.map_map (measurable_chartOf t0) (measurable_addDig a),
    haar_map_addDig]

/-- The charts of the law: legal, of typical quarter phase, with the cutoff `[r < cut]`. -/
def GoodChart (U : Machine) (n0 k cut : ℕ) (c : Plane → RTile (contentP U n0) k) : Prop :=
  IsRChart (contentP U n0) k c ∧ Typical (qphaseOf (quartersOf c)) ∧
    (∀ ξ, (c ξ).1.1.q.V = decide (prankOf (col (qphaseOf (quartersOf c))) ξ.1 < cut)) ∧
    (∀ ξ, (c ξ).1.1.q.H = decide (prankOf (row (qphaseOf (quartersOf c))) ξ.2 < cut))

theorem measurableSet_goodChart : MeasurableSet {c | GoodChart U n0 k cut c} := by
  have hφ : Measurable fun c : Plane → RTile (contentP U n0) k => qphaseOf (quartersOf c) :=
    measurable_qphaseOf.comp measurable_quartersOf
  have hV : ∀ ξ, MeasurableSet {c : Plane → RTile (contentP U n0) k |
      (c ξ).1.1.q.V = decide (prankOf (col (qphaseOf (quartersOf c))) ξ.1 < cut)} := fun ξ => by
    have e : {c : Plane → RTile (contentP U n0) k |
        (c ξ).1.1.q.V = decide (prankOf (col (qphaseOf (quartersOf c))) ξ.1 < cut)} =
        ⋃ r : ℕ, {c | (c ξ).1.1.q.V = decide (r < cut)} ∩
          (fun c => qphaseOf (quartersOf c)) ⁻¹' {τ | prankOf (col τ) ξ.1 = r} := by
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
      exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨r, h, hr⟩ => by rw [hr]; exact h⟩
    rw [e]
    refine MeasurableSet.iUnion fun r => ?_
    have hs : MeasurableSet {t : RTile (contentP U n0) k | t.1.1.q.V = decide (r < cut)} :=
      MeasurableSet.of_discrete
    exact (measurable_pi_apply ξ hs).inter (hφ (mlevel_prankOf_col ξ.1 r))
  have hH : ∀ ξ, MeasurableSet {c : Plane → RTile (contentP U n0) k |
      (c ξ).1.1.q.H = decide (prankOf (row (qphaseOf (quartersOf c))) ξ.2 < cut)} := fun ξ => by
    have e : {c : Plane → RTile (contentP U n0) k |
        (c ξ).1.1.q.H = decide (prankOf (row (qphaseOf (quartersOf c))) ξ.2 < cut)} =
        ⋃ r : ℕ, {c | (c ξ).1.1.q.H = decide (r < cut)} ∩
          (fun c => qphaseOf (quartersOf c)) ⁻¹' {τ | prankOf (row τ) ξ.2 = r} := by
      ext c
      simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_inter_iff, Set.mem_preimage]
      exact ⟨fun h => ⟨_, h, rfl⟩, fun ⟨r, h, hr⟩ => by rw [hr]; exact h⟩
    rw [e]
    refine MeasurableSet.iUnion fun r => ?_
    have hs : MeasurableSet {t : RTile (contentP U n0) k | t.1.1.q.H = decide (r < cut)} :=
      MeasurableSet.of_discrete
    exact (measurable_pi_apply ξ hs).inter (hφ (mlevel_prankOf_row ξ.2 r))
  have hV' := MeasurableSet.iInter hV
  have hH' := MeasurableSet.iInter hH
  rw [← Set.ofPred_forall] at hV' hH'
  exact (measurableSet_legalOn_univ _ _).inter ((hφ measurableSet_typical).inter (hV'.inter hH'))

/-- For a typical phase the chart is good, with quarter phase `τ`. -/
theorem goodChart_chartOf {τ : ℕ → Bool × Bool} (hτ : Typical τ) (hN : NHalt U n0 cut)
    (t0 : RTile (contentP U n0) k) : GoodChart U n0 k cut (chartOf U n0 k cut τ t0) := by
  have hq : quartersOf (chartOf U n0 k cut τ t0) = qtilingOf τ := chartOf_quarters hτ hN t0
  have hφ : qphaseOf (quartersOf (chartOf U n0 k cut τ t0)) = τ := by
    rw [hq]; exact (quarterSystem.Ψ_mem τ hτ.1).2
  rw [GoodChart, hφ]
  exact ⟨chartOf_isRChart hτ hN t0, hτ, chartOf_V hτ hN t0, chartOf_H hτ hN t0⟩

/-- Almost every chart of the law is good. -/
theorem ae_goodChart (hN : NHalt U n0 cut) (t0 : RTile (contentP U n0) k) :
    ∀ᵐ c ∂(chartLaw U n0 k cut t0), GoodChart U n0 k cut c := by
  rw [chartLaw, ae_map_iff (measurable_chartOf t0).aemeasurable measurableSet_goodChart]
  filter_upwards [ae_typical] with τ hτ
  exact goodChart_chartOf hτ hN t0

/-- **Prop 4.3, the nonhalting branch.** If `U` does not halt on `n ≥ 1`, `n₀ ≥ 1` and the cutoff
is `2a - 2` or `2a - 1` (`a = n + n₀`), there is a translation-invariant probability law of
legal `R`-charts whose quarter phase is typical and whose rank flags are the cutoff `[r < cut]`
(row flag one on the bottom rows of depths `d < a`, zero on depths `d ≥ a`,
`chartOf_bottom_flag`). -/
theorem chart_law_exists (hN : NHalt U n0 cut) :
    ∃ μ : Measure (Plane → RTile (contentP U n0) k), IsProbabilityMeasure μ ∧
      (∀ a, μ.map (UPD.shift a) = μ) ∧ ∀ᵐ c ∂μ, GoodChart U n0 k cut c := by
  obtain ⟨τ0, hτ0⟩ := ae_typical.exists
  let t0 : RTile (contentP U n0) k := ⟨rawOf U n0 k cut τ0 0, raw_tileOK hτ0 hN 0⟩
  exact ⟨chartLaw U n0 k cut t0, isProbabilityMeasure_chartLaw t0, chartLaw_shift t0,
    ae_goodChart hN t0⟩

end Law

end UND.Chart
