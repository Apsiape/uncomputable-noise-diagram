/-
# Prop 4.3, the halting branch: a wrong flag in every legal chart, in every phase (M6)

Node M6 of `BLUEPRINT.md` (Part A.4), NEW.

Paper (Prop 4.3): "For `a = n + n₀`, … If `U(n)` halts, every legal chart in every phase has a
depth-`(a-1)` bottom end with flag zero or a depth-`a` bottom end with flag one." Proof (halting):
"avoiding both asserted wrong flags would impose the two rank conditions of Lemma 4.2, since every
finite depth has bottom corners in every phase. Every `d > a` board would decode `n`. The decoding
and the halting computation have finite time and space budgets. Choose `d` with `N_d` larger than
the elapsed time and largest visited address. Lemma 3.3 forces its computation, including HALT at a
stored time column, contradicting (10). Both critical depths are gated since `a - 1 ≥ k`."

* `IsBottomEnd τ d ξ` (`ξ = (R_d(z), Bot_d(z'))`), `prank_frameLo` (a depth-`d` lower endpoint has
  parent rank `2d - 1`, every phase), `isEnd_of_bottomEnd` (it is an `End`);
* **`chart_wrong_flag`** (Prop 4.3, halting): for every legal chart of `R` (content `P`), in every
  phase, if `U` halts on `n ≥ 1` (`n₀ ≥ 1`), there is an `End` at a depth-`(a-1)` bottom end with
  flag `H_row = 0` or at a depth-`a` bottom end with flag `H_row = 1`;
* **`bottomEnd_gate`** (the critical depths are gated): at a depth-`d` bottom end with `k ≤ d`
  the decoded lane phase is zero (FD2's restricted form, every phase).
-/
import UncomputableNoiseDiagram.Chart.BoardRun

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UND.Chart

open UPD UPD.Scaffold

/-- A depth-`d` bottom end: `ξ = (R_d(z), Bot_d(z'))`. -/
def IsBottomEnd (τ : ℕ → Bool × Bool) (d : ℕ) (ξ : Plane) : Prop :=
  IsRightEnd (phaseOffsets (col τ)) d ξ.1 ∧ IsLeftEnd (phaseOffsets (row τ)) d ξ.2

/-- The lower endpoint of a depth-`d` frame has parent rank `2d - 1` (every phase). -/
theorem prank_frameLo (t : ℕ → Bool) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) :
    PRank t (frameLo (phaseOffsets t) d m) (2 * d - 1) := by
  obtain ⟨j, hj⟩ : ∃ j, 2 * d = j + 1 := ⟨2 * d - 1, by omega⟩
  rw [show 2 * d - 1 = j by omega]
  refine prank_of_half t d _ (by omega) 0 (2 * m) ?_
  have e4 : (4 : ℤ) ^ d = 2 * 2 ^ j := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, hj, pow_succ]; ring
  simp only [frameLo]
  rw [show phaseOffsets t d + (4 * m + 1) * 4 ^ d + 1 - phaseOffsets t d =
      2 * ((4 * m + 1) * 2 ^ j) + 1 by rw [e4]; ring,
    show ∀ X : ℤ, (2 * X + 1) / 2 = X from fun X => by omega]
  ring

variable {S : Type} [Fintype S] [DecidableEq S] {C : ContentOps S} {k : ℕ}
  {c : Plane → RTile C k} {τ : ℕ → Bool × Bool}

/-- A bottom end of depth `d ≥ 1` is an `End` (every phase). -/
theorem isEnd_of_bottomEnd (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ) {d : ℕ} (hd : 1 ≤ d)
    {ξ : Plane} (hb : IsBottomEnd τ d ξ) : IsEnd (c ξ).1.1.q.toQ := by
  obtain ⟨m, hm⟩ := hb.2
  have hr : PRank (row τ) ξ.2 (2 * d - 1) := by rw [hm]; exact prank_frameLo (row τ) hd m
  exact (end_iff hτ ξ (Or.inr ⟨_, hr⟩)).2 ⟨d, hd, hb.1, hb.2⟩

/-- **The critical depths are gated**: at a depth-`d` bottom end with `k ≤ d` the decoded lane
phase is zero (every phase). -/
theorem bottomEnd_gate (hc : IsRChart C k c) (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ)
    {d : ℕ} {ξ : Plane} (hb : IsBottomEnd τ d ξ) (hk : k ≤ d) :
    (chartData C k).phase (c ξ) = 0 := by
  obtain ⟨m, hm⟩ := hb.2
  rw [hc.phase_eq_zero_iff hτ ξ, hm]
  exact (lanePhase_bot_eq_zero_iff (row τ) k d m).2 hk

/-- **Prop 4.3, the halting branch** (every phase): if `U` halts on `n ≥ 1` (with `n₀ ≥ 1`), every
legal chart of `R` with the content of `P` has an `End` at a depth-`(a-1)` bottom end with flag
`H_row = 0`, or at a depth-`a` bottom end with flag `H_row = 1`, where `a = n + n₀`. -/
theorem chart_wrong_flag {U : Machine} {n0 : ℕ} {c : Plane → RTile (contentP U n0) k}
    (hc : IsRChart (contentP U n0) k c) (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ) {n : ℕ}
    (hn : 1 ≤ n) (hn0 : 1 ≤ n0) (hU : U.HaltsOn n) :
    (∃ ξ, IsEnd (c ξ).1.1.q.toQ ∧ IsBottomEnd τ (n + n0 - 1) ξ ∧ (c ξ).1.1.q.H = false) ∨
      (∃ ξ, IsEnd (c ξ).1.1.q.toQ ∧ IsBottomEnd τ (n + n0) ξ ∧ (c ξ).1.1.q.H = true) := by
  classical
  by_contra hcon
  rw [not_or, not_exists, not_exists] at hcon
  obtain ⟨h1, h0⟩ := hcon
  set a := n + n0 with ha
  have ha2 : 2 ≤ a := by omega
  -- the two critical bottom ends at `z = z' = 0`
  let ξ₁ : Plane :=
    (frameHi (phaseOffsets (col τ)) (a - 1) 0, frameLo (phaseOffsets (row τ)) (a - 1) 0)
  let ξ₀ : Plane := (frameHi (phaseOffsets (col τ)) a 0, frameLo (phaseOffsets (row τ)) a 0)
  have hb₁ : IsBottomEnd τ (a - 1) ξ₁ := ⟨⟨0, rfl⟩, ⟨0, rfl⟩⟩
  have hb₀ : IsBottomEnd τ a ξ₀ := ⟨⟨0, rfl⟩, ⟨0, rfl⟩⟩
  have hH₁ : (c ξ₁).1.1.q.H = true := by
    have := h1 ξ₁
    simp only [not_and, Bool.not_eq_false] at this
    exact this (isEnd_of_bottomEnd hτ (by omega) hb₁) hb₁
  have hH₀ : (c ξ₀).1.1.q.H = false := by
    have := h0 ξ₀
    simp only [not_and, Bool.not_eq_true] at this
    exact this (isEnd_of_bottomEnd hτ (by omega) hb₀) hb₀
  have hr₁ : PRank (row τ) ξ₁.2 (2 * a - 3) := by
    rw [show 2 * a - 3 = 2 * (a - 1) - 1 by omega]
    exact prank_frameLo (row τ) (by omega) 0
  have hr₀ : PRank (row τ) ξ₀.2 (2 * a - 1) := prank_frameLo (row τ) (by omega) 0
  obtain ⟨b, hb, hb3, hb1, hbr⟩ := cutoff_of_flags hc.isDTiling hτ hr₁ hH₁ hr₀ hH₀
  -- `U` halts on `e - n₀ - 1 = n`, `e = a + 1`: one time `T` for every decoding board
  have he : n0 + 2 ≤ a + 1 := by omega
  have hU' : U.HaltsOn (a + 1 - n0 - 1) := by rw [show a + 1 - n0 - 1 = n by omega]; exact hU
  obtain ⟨T, hT⟩ := MachineP.decode_halts (U := U) (n0 := n0) (a + 1) he hU'
  -- a board of depth `d > a` with `N_d > T`
  set d := a + T + 1 with hd
  have hd1 : 1 ≤ d := by omega
  have had : a < d := by omega
  have hTN : T < Nd d := by
    have := Nat.lt_two_pow_self (n := d + 2)
    show T < 2 ^ (d + 2) - 2
    omega
  -- Lemma 4.2: its input decodes `n`
  set p := FreeOff (row τ) d 0 with hp
  have hcount : Nat.count p (4 ^ a - 2) = 2 ^ (a + 1) - 2 :=
    count_initial_zero (row τ) (by omega) had 0
  obtain ⟨hfree, -, -⟩ := initial_zero (row τ) ha2 had 0
  have hnth : Nat.nth p (2 ^ (a + 1) - 2) = 4 ^ a - 2 := by
    rw [← hcount]; exact Nat.nth_count hfree
  have hjN : 2 ^ (a + 1) - 2 < Nd d := by
    have : 2 ^ (a + 1) < 2 ^ (d + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    show 2 ^ (a + 1) - 2 < 2 ^ (d + 2) - 2
    have : 2 ≤ 2 ^ (a + 1) := Nat.le_self_pow (by omega) 2
    omega
  obtain ⟨hlow, hzero, hpi⟩ := input_read_large (Z := fun ξ => (c ξ).1.1.q) hτ hb ha2 had hb3 hb1
    hbr 0 (freeAt (col τ) d 0 0)
  have hdec : MachineP.Decodes (a + 1) (boardH c τ d 0 0) (boardPi c τ d 0 0) := by
    refine ⟨fun j hj => ?_, ?_, ?_⟩
    · have hjN' : j < Nd d := by omega
      have hlt : Nat.nth p j < 4 ^ a - 2 := by
        rw [← hnth]
        exact Nat.nth_lt_nth_of_lt_card (freeOff_finite (row τ) d 0) hj
          (by rw [card_freeOff (row τ) hd1 0]; exact hjN)
      exact hlow _ hlt (freeOff_nth (row τ) hd1 0 hjN')
    · simp only [boardH, freeAt]
      rw [← hp, hnth]
      exact hzero
    · simp only [boardPi, freeAt]
      rw [← hp, hnth]
      exact hpi
  -- HALT at time `T` on the board, against the tableau (10)
  obtain ⟨j, hj⟩ := MachineP.runP_halts (N := Nd d) _ _ (hT _ _ hdec) hTN
  obtain ⟨tS, tN, hk⟩ := board_run hc hτ hd1 0 0 T hTN j
  obtain ⟨tS', tC', tN', hk', -, htab⟩ := board_record hc hτ hd1 0 0
    (freeAt_free (col τ) hd1 0 hTN) (freeAt_free (row τ) hd1 0 j.2)
  rw [hk] at hk'
  simp only [Option.some.injEq, Prod.mk.injEq] at hk'
  obtain ⟨-, rfl, -⟩ := hk'
  have h8 : MachineP.CarriesHalt U n0
      (MachineP.runP U n0 (Nd d) (boardH c τ d 0 0) (boardPi c τ d 0 0) T j) = false :=
    htab.2.2.2.2.2.2.2.1
  rw [h8] at hj
  exact Bool.false_ne_true hj

end UND.Chart
