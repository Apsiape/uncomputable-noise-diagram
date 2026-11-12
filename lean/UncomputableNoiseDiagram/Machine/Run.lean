/-
# Lemma 4.1(a): `f_P` is the sequential machine `P` (M2)

Node M2 of `BLUEPRINT.md` (Part A.4), ADAPTED from the hard-model core
(`UndecidablePhaseDiagram/Background/Machine.lean`: `nextRow_stay/up/down(_fail)`;
`Background/Run.lean`: `MCfg`, `stepU`, `stepB`, `colOf`, `nextRow_colOf`, `runM_eq`,
`stepB_iterate`), for the ordered rule `f_P` of `Machine/P.lean`. One difference (D28(d),
ACCEPTED by QB, s5): a failing head at a tape end keeps the symbol its transition wrote.

Paper (Lemma 4.1, first sentence, and proof, first paragraph): "On a finite tape initialized
above, `f_P` gives exactly the sequential `P` computation, with one head at every time and absorbing
failure on an attempted exit. … A stay step changes just the head cell. For an interior move the
old head cell loses the head and exactly its destination receives the new state, retaining the
destination's own tape symbol. Every other cell preserves its symbol. An exit leaves the head at the
boundary in FAIL. Induction gives the one-head assertion and excludes the malformed priorities."

* `nextRow` (one row of the board recursion `s_{i+1}(j) = f_P(s_i(j-1), s_i(j), s_i(j+1))`, `⊥`
  beyond both ends), `oneHead`;
* **`nextRow_stay`**, **`nextRow_up`**, **`nextRow_down`**, **`nextRow_up_fail`**,
  **`nextRow_down_fail`** (the one-head step);
* `PCfg` (tape `ℕ → Tape U`, head, state), `stepU` (one step of `P` on the tape `ℕ`; a move down
  from cell `0` fails in place), `stepB N` (on `[0, N)`; a move up from `N - 1` fails in place),
  `colOf`;
* **`nextRow_colOf`**, `nextRow_iterate`, **`runP_eq`** (Lemma 4.1(a): the board recursion from
  `init` is the column of the bounded run of `P` from SCAN at cell `0`);
* `stepB_iterate` (bounded and unbounded runs agree until the first exit, after which the bounded
  run is in FAIL), **`stepB_iterate_eq`** (no exit: they agree), `stepU_iterate_fail`.
-/
import UncomputableNoiseDiagram.Machine.P

set_option autoImplicit false

namespace UND.MachineP

open UPD

variable {U : Machine} {n0 : ℕ}

/-- One row of the board computation on the cells `0, …, N - 1` (`⊥` beyond both ends): cell `j`
becomes `f_P(row(j-1), row(j), row(j+1))`. -/
def nextRow {N : ℕ} (row : Fin N → Cell U n0) (i : Fin N) : Cell U n0 :=
  fP U n0 (if h : 0 < i.val then some (row ⟨i.val - 1, by omega⟩) else none) (row i)
    (if h : i.val + 1 < N then some (row ⟨i.val + 1, h⟩) else none)

/-- A row with exactly one head, at `h`, in state `q`, on the tape `t`. -/
def oneHead {N : ℕ} (t : Fin N → Tape U) (h : Fin N) (q : PState U n0) : Fin N → Cell U n0 :=
  fun i => (t i, if i = h then some q else none)

/-- **One-head invariant, move up.** -/
theorem nextRow_up {N : ℕ} (t : Fin N → Tape U) (h : Fin N) (q : PState U n0)
    (hD : (deltaP U n0 q (t h)).2.2 = .up) (hh : h.val + 1 < N) :
    nextRow (oneHead t h q) =
      oneHead (Function.update t h (deltaP U n0 q (t h)).2.1) ⟨h.val + 1, hh⟩
        (deltaP U n0 q (t h)).1 := by
  funext i
  by_cases hi : i = h
  · subst hi
    have hne : i ≠ ⟨i.val + 1, hh⟩ := fun h' => by
      have := congrArg Fin.val h'; simp at this
    simp [nextRow, oneHead, fP, hD, hh, hne]
  · by_cases hi1 : i.val = h.val + 1
    · have hpos : 0 < i.val := by omega
      have hprev : (⟨i.val - 1, by omega⟩ : Fin N) = h := Fin.ext (by simp; omega)
      have hieq : i = ⟨h.val + 1, hh⟩ := Fin.ext hi1
      have hup : Function.update t h (deltaP U n0 q (t h)).2.1 i = t i :=
        Function.update_of_ne hi _ _
      simp only [nextRow, oneHead, fP, ite_eq_right hi, dite_eq_left hpos, hprev, fromBelow, hup,
        ite_eq_left hieq]
      simp [hD]
    · have hieq : i ≠ ⟨h.val + 1, hh⟩ := fun h' => hi1 (by rw [h'])
      have hbelow : ∀ hp : 0 < i.val, (⟨i.val - 1, by omega⟩ : Fin N) ≠ h := fun hp h' => by
        have := congrArg Fin.val h'; simp at this; omega
      have habove : ∀ ha : i.val + 1 < N, (⟨i.val + 1, ha⟩ : Fin N) = h →
          fromAbove U n0 (some (t h, some q)) = none := fun _ _ => by
        simp [fromAbove, hD]
      simp only [nextRow, oneHead, fP, ite_eq_right hi, ite_eq_right hieq, Function.update_of_ne hi]
      split_ifs with h1 h2 h3 <;> simp_all [fromBelow, fromAbove]

/-- **One-head invariant, stay.** -/
theorem nextRow_stay {N : ℕ} (t : Fin N → Tape U) (h : Fin N) (q : PState U n0)
    (hD : (deltaP U n0 q (t h)).2.2 = .stay) :
    nextRow (oneHead t h q) =
      oneHead (Function.update t h (deltaP U n0 q (t h)).2.1) h (deltaP U n0 q (t h)).1 := by
  funext i
  by_cases hi : i = h
  · subst hi
    simp [nextRow, oneHead, fP, hD]
  · have hb : ∀ g : Tape U, ∀ q₀ : PState U n0, (deltaP U n0 q₀ g).2.2 = .stay →
        fromBelow U n0 (some (g, some q₀)) = none := fun g q₀ h' => by simp [fromBelow, h']
    have ha : ∀ g : Tape U, ∀ q₀ : PState U n0, (deltaP U n0 q₀ g).2.2 = .stay →
        fromAbove U n0 (some (g, some q₀)) = none := fun g q₀ h' => by simp [fromAbove, h']
    simp only [nextRow, oneHead, fP, ite_eq_right hi, Function.update_of_ne hi]
    split_ifs with h1 h2 h3 h4 <;> simp_all [fromBelow, fromAbove]

/-- **One-head invariant, move down.** -/
theorem nextRow_down {N : ℕ} (t : Fin N → Tape U) (h : Fin N) (q : PState U n0)
    (hD : (deltaP U n0 q (t h)).2.2 = .down) (hh : 0 < h.val) :
    nextRow (oneHead t h q) =
      oneHead (Function.update t h (deltaP U n0 q (t h)).2.1) ⟨h.val - 1, by omega⟩
        (deltaP U n0 q (t h)).1 := by
  funext i
  by_cases hi : i = h
  · subst hi
    have hne : i ≠ ⟨i.val - 1, by omega⟩ := fun h' => by
      have := congrArg Fin.val h'; simp at this; omega
    simp [nextRow, oneHead, fP, hD, hh, hne]
  · by_cases hi1 : i.val + 1 = h.val
    · have hlt : i.val + 1 < N := by omega
      have hnext : (⟨i.val + 1, hlt⟩ : Fin N) = h := Fin.ext (by simp; omega)
      have hieq : i = ⟨h.val - 1, by omega⟩ := Fin.ext (by simp; omega)
      have hup : Function.update t h (deltaP U n0 q (t h)).2.1 i = t i :=
        Function.update_of_ne hi _ _
      have hbelow : ∀ hp : 0 < i.val, (⟨i.val - 1, by omega⟩ : Fin N) ≠ h := fun hp h' => by
        have := congrArg Fin.val h'; simp at this; omega
      simp only [nextRow, oneHead, fP, ite_eq_right hi, dite_eq_left hlt, hnext, hup, ite_eq_left hieq]
      split_ifs with h1 <;> simp_all [fromBelow, fromAbove]
    · have hieq : i ≠ ⟨h.val - 1, by omega⟩ := fun h' => hi1 (by rw [h']; simp; omega)
      have habove : ∀ ha : i.val + 1 < N, (⟨i.val + 1, ha⟩ : Fin N) ≠ h := fun ha h' => by
        have := congrArg Fin.val h'; simp at this; omega
      have hb : fromBelow U n0 (some (t h, some q)) = none := by simp [fromBelow, hD]
      simp only [nextRow, oneHead, fP, ite_eq_right hi, ite_eq_right hieq, Function.update_of_ne hi]
      split_ifs with h1 h2 h3 h4 <;> simp_all [fromBelow, fromAbove]

/-- **One-head invariant, exit at the top**: a head that would leave the row upwards writes its
symbol and enters FAIL in place (D28(d)). -/
theorem nextRow_up_fail {N : ℕ} (t : Fin N → Tape U) (h : Fin N) (q : PState U n0)
    (hD : (deltaP U n0 q (t h)).2.2 = .up) (hh : h.val + 1 = N) :
    nextRow (oneHead t h q) =
      oneHead (Function.update t h (deltaP U n0 q (t h)).2.1) h .fail := by
  funext i
  by_cases hi : i = h
  · subst hi
    have hn : ¬ (i.val + 1 < N) := by omega
    simp [nextRow, oneHead, fP, hD, hn]
  · have hbelow : ∀ hp : 0 < i.val, (⟨i.val - 1, by omega⟩ : Fin N) ≠ h := fun hp h' => by
      have := congrArg Fin.val h'; simp at this; have := i.2; omega
    have ha : fromAbove U n0 (some (t h, some q)) = none := by simp [fromAbove, hD]
    simp only [nextRow, oneHead, fP, ite_eq_right hi, Function.update_of_ne hi]
    split_ifs with h1 h2 h3 h4 <;> simp_all [fromBelow, fromAbove]

/-- **One-head invariant, exit at the bottom**: a head that would leave the row downwards writes
its symbol and enters FAIL in place (D28(d)). -/
theorem nextRow_down_fail {N : ℕ} (t : Fin N → Tape U) (h : Fin N) (q : PState U n0)
    (hD : (deltaP U n0 q (t h)).2.2 = .down) (hh : h.val = 0) :
    nextRow (oneHead t h q) =
      oneHead (Function.update t h (deltaP U n0 q (t h)).2.1) h .fail := by
  funext i
  by_cases hi : i = h
  · subst hi
    have hn : ¬ (0 < i.val) := by omega
    simp [nextRow, oneHead, fP, hD, hn]
  · have habove : ∀ ha : i.val + 1 < N, (⟨i.val + 1, ha⟩ : Fin N) ≠ h := fun ha h' => by
      have := congrArg Fin.val h'; simp at this; omega
    have hb : fromBelow U n0 (some (t h, some q)) = none := by simp [fromBelow, hD]
    simp only [nextRow, oneHead, fP, ite_eq_right hi, Function.update_of_ne hi]
    split_ifs with h1 h2 h3 h4 <;> simp_all [fromBelow, fromAbove]

/-! ## The sequential machine -/

/-- A configuration of `P`: tape (cells `0, 1, 2, …`), head cell, state. -/
structure PCfg (U : Machine) (n0 : ℕ) where
  /-- the tape -/
  tape : ℕ → Tape U
  /-- the head cell -/
  head : ℕ
  /-- the state -/
  state : PState U n0

/-- One step of `P` on the tape `ℕ`: `δ_P(q, g) = (q', g', D)`; write `g'`, enter `q'`, move by
`D`; a move down from cell `0` writes `g'` and enters FAIL in place. -/
def stepU (c : PCfg U n0) : PCfg U n0 :=
  match (deltaP U n0 c.state (c.tape c.head)).2.2 with
  | .stay => ⟨Function.update c.tape c.head (deltaP U n0 c.state (c.tape c.head)).2.1, c.head,
      (deltaP U n0 c.state (c.tape c.head)).1⟩
  | .up => ⟨Function.update c.tape c.head (deltaP U n0 c.state (c.tape c.head)).2.1, c.head + 1,
      (deltaP U n0 c.state (c.tape c.head)).1⟩
  | .down => if c.head = 0 then
      ⟨Function.update c.tape c.head (deltaP U n0 c.state (c.tape c.head)).2.1, c.head, .fail⟩
    else
      ⟨Function.update c.tape c.head (deltaP U n0 c.state (c.tape c.head)).2.1, c.head - 1,
        (deltaP U n0 c.state (c.tape c.head)).1⟩

/-- One step of `P` on the tape `[0, N)`: as `stepU`, except that a move up from cell `N - 1`
writes and enters FAIL in place. -/
def stepB (N : ℕ) (c : PCfg U n0) : PCfg U n0 :=
  if (deltaP U n0 c.state (c.tape c.head)).2.2 = .up ∧ N ≤ c.head + 1 then
    ⟨Function.update c.tape c.head (deltaP U n0 c.state (c.tape c.head)).2.1, c.head, .fail⟩
  else stepU c

/-- The column of a configuration on the cells `0, …, N - 1`: the tape, with the state at the head
cell and the no-head mark elsewhere. -/
def colOf (N : ℕ) (c : PCfg U n0) : Fin N → Cell U n0 :=
  fun i => (c.tape i, if i.val = c.head then some c.state else none)

theorem colOf_eq {N : ℕ} (c : PCfg U n0) (hc : c.head < N) :
    colOf N c = oneHead (fun i : Fin N => c.tape i) ⟨c.head, hc⟩ c.state := by
  funext i
  simp only [colOf, oneHead, Fin.ext_iff]

theorem update_restrict {N : ℕ} (t : ℕ → Tape U) (h : ℕ) (hh : h < N) (g : Tape U) :
    (fun i : Fin N => Function.update t h g i.val) =
      Function.update (fun i : Fin N => t i) ⟨h, hh⟩ g := by
  funext i
  by_cases hi : i.val = h
  · have : i = ⟨h, hh⟩ := Fin.ext hi
    subst this; simp
  · rw [Function.update_of_ne hi, Function.update_of_ne (fun h' => hi (by rw [h']))]

/-- **Lemma 4.1(a), the induction step**: one row of the board recursion on a column with one
head is one step of `P` on `[0, N)`, an attempted exit through either end failing in place. -/
theorem nextRow_colOf {N : ℕ} (c : PCfg U n0) (hc : c.head < N) :
    (stepB N c).head < N ∧ nextRow (colOf N c) = colOf N (stepB N c) := by
  obtain ⟨t, h, q⟩ := c
  simp only at hc
  rw [colOf_eq _ hc]
  rcases hD : (deltaP U n0 q (t h)).2.2 with _ | _ | _
  · -- up
    by_cases hN : N ≤ h + 1
    · have hs : stepB N ⟨t, h, q⟩ =
          ⟨Function.update t h (deltaP U n0 q (t h)).2.1, h, .fail⟩ := by simp [stepB, hD, hN]
      rw [hs]
      refine ⟨hc, ?_⟩
      rw [colOf_eq _ hc, update_restrict _ _ hc]
      exact nextRow_up_fail (fun i : Fin N => t i) ⟨h, hc⟩ q hD (by simp; omega)
    · have hh : h + 1 < N := by omega
      have hs : stepB N ⟨t, h, q⟩ =
          ⟨Function.update t h (deltaP U n0 q (t h)).2.1, h + 1, (deltaP U n0 q (t h)).1⟩ := by
        simp only [stepB, hD, true_and, ite_eq_right hN, stepU]
      rw [hs]
      refine ⟨hh, ?_⟩
      rw [colOf_eq _ hh, update_restrict _ _ hc]
      exact nextRow_up (fun i : Fin N => t i) ⟨h, hc⟩ q hD hh
  · -- down
    by_cases h0 : h = 0
    · subst h0
      have hs : stepB N ⟨t, 0, q⟩ =
          ⟨Function.update t 0 (deltaP U n0 q (t 0)).2.1, 0, .fail⟩ := by
        simp [stepB, stepU, hD]
      rw [hs]
      refine ⟨hc, ?_⟩
      rw [colOf_eq _ hc, update_restrict _ _ hc]
      exact nextRow_down_fail (fun i : Fin N => t i) ⟨0, hc⟩ q hD rfl
    · have hs : stepB N ⟨t, h, q⟩ =
          ⟨Function.update t h (deltaP U n0 q (t h)).2.1, h - 1, (deltaP U n0 q (t h)).1⟩ := by
        simp [stepB, stepU, hD, h0]
      rw [hs]
      refine ⟨show h - 1 < N by omega, ?_⟩
      rw [colOf_eq _ (by omega : h - 1 < N), update_restrict _ _ hc]
      exact nextRow_down (fun i : Fin N => t i) ⟨h, hc⟩ q hD (by simp; omega)
  · -- stay
    have hs : stepB N ⟨t, h, q⟩ =
        ⟨Function.update t h (deltaP U n0 q (t h)).2.1, h, (deltaP U n0 q (t h)).1⟩ := by
      simp [stepB, stepU, hD]
    rw [hs]
    refine ⟨hc, ?_⟩
    rw [colOf_eq _ hc, update_restrict _ _ hc]
    exact nextRow_stay (fun i : Fin N => t i) ⟨h, hc⟩ q hD

/-- Iterating the induction step. -/
theorem nextRow_iterate {N : ℕ} (c : PCfg U n0) (hc : c.head < N) (i : ℕ) :
    ((stepB N)^[i] c).head < N ∧ nextRow^[i] (colOf N c) = colOf N ((stepB N)^[i] c) := by
  induction i with
  | zero => exact ⟨hc, rfl⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply', ih.2]
    exact nextRow_colOf _ ih.1

/-! ## The board run (Lemma 4.1(a)) -/

/-- The initial tape: `h_in = h j`, `π = π j`, `z = [j = 0]`, the work tracks zero or blank. -/
def tape0 (U : Machine) (h pi : ℕ → Bool) : ℕ → Tape U :=
  fun j => ⟨h j, pi j, decide (j = 0), false, false, 0, 0⟩

/-- The initial configuration: the tape `tape0`, the head at cell `0` in SCAN. -/
def cfg0 (U : Machine) (n0 : ℕ) (h pi : ℕ → Bool) : PCfg U n0 := ⟨tape0 U h pi, 0, .scan⟩

/-- The board run of Lemma 3.3 on `N` cells: `s_0(j) = init(h j, π j, [j = 0])`,
`s_{i+1}(j) = f_P(s_i(j-1), s_i(j), s_i(j+1))`, `s_i(-1) = s_i(N) = ⊥`. -/
def runP (U : Machine) (n0 N : ℕ) (h pi : ℕ → Bool) (i : ℕ) : Fin N → Cell U n0 :=
  nextRow^[i] (fun j => initP U n0 (h j.val) (pi j.val) (decide (j.val = 0)))

/-- **Lemma 4.1(a)**: on a tape of `N ≥ 1` cells initialized by `init`, the board recursion is
exactly the column of the sequential run of `P` from SCAN at cell `0`, with one head at every time
and failure in place on an attempted exit. -/
theorem runP_eq (U : Machine) (n0 : ℕ) {N : ℕ} (hN : 1 ≤ N) (h pi : ℕ → Bool) (i : ℕ) :
    runP U n0 N h pi i = colOf N ((stepB N)^[i] (cfg0 U n0 h pi)) := by
  have h0 : (fun j : Fin N => initP U n0 (h j.val) (pi j.val) (decide (j.val = 0))) =
      colOf N (cfg0 U n0 h pi) := by
    funext j
    simp only [initP, colOf, cfg0, tape0]
    by_cases hj : j.val = 0 <;> simp [hj]
  rw [runP, h0]
  exact (nextRow_iterate (cfg0 U n0 h pi) (by simp [cfg0]; omega) i).2

/-! ## Bounded and unbounded runs -/

theorem deltaP_fail (g : Tape U) : deltaP U n0 .fail g = (.fail, g, .stay) := by
  simp [deltaP, program]

theorem deltaP_halt (g : Tape U) : deltaP U n0 .halt g = (.halt, g, .stay) := by
  simp [deltaP, program]

/-- FAIL is absorbing for `stepU`. -/
theorem stepU_fail (t : ℕ → Tape U) (h : ℕ) :
    stepU (⟨t, h, .fail⟩ : PCfg U n0) = ⟨t, h, .fail⟩ := by
  simp [stepU, deltaP_fail]

theorem stepU_iterate_fail (t : ℕ → Tape U) (h k : ℕ) :
    (stepU)^[k] (⟨t, h, .fail⟩ : PCfg U n0) = ⟨t, h, .fail⟩ := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih, stepU_fail]

/-- FAIL is absorbing for `stepB`. -/
theorem stepB_fail {N : ℕ} (t : ℕ → Tape U) (h : ℕ) :
    stepB N (⟨t, h, .fail⟩ : PCfg U n0) = ⟨t, h, .fail⟩ := by
  simp [stepB, stepU, deltaP_fail]

/-- HALT is absorbing for `stepU`. -/
theorem stepU_halt (t : ℕ → Tape U) (h : ℕ) :
    stepU (⟨t, h, .halt⟩ : PCfg U n0) = ⟨t, h, .halt⟩ := by
  simp [stepU, deltaP_halt]

/-- Bounded and unbounded runs agree until the first exit: after `k` steps the bounded run is the
unbounded one, or it is in FAIL. -/
theorem stepB_iterate (N : ℕ) (c : PCfg U n0) (k : ℕ) :
    (stepB N)^[k] c = (stepU)^[k] c ∨ ((stepB N)^[k] c).state = .fail := by
  induction k with
  | zero => exact Or.inl rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    rcases ih with h | h
    · rw [h]
      by_cases hx : (deltaP U n0 ((stepU)^[k] c).state (((stepU)^[k] c).tape
          ((stepU)^[k] c).head)).2.2 = .up ∧ N ≤ ((stepU)^[k] c).head + 1
      · right; simp [stepB, hx]
      · left; simp only [stepB, ite_eq_right hx]
    · right
      generalize (stepB N)^[k] c = c' at h ⊢
      obtain ⟨t, hh, q⟩ := c'
      simp only at h
      subst h
      rw [stepB_fail]

/-- **No exit, no difference**: if every head of the unbounded run before step `k` is below
`N - 1`, the bounded run on `[0, N)` agrees with it at step `k`. -/
theorem stepB_iterate_eq (N : ℕ) (c : PCfg U n0) (k : ℕ)
    (hk : ∀ k' < k, ((stepU)^[k'] c).head + 1 < N) :
    (stepB N)^[k] c = (stepU)^[k] c := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply',
      ih (fun k' hk' => hk k' (by omega))]
    have hx : ¬ ((deltaP U n0 ((stepU)^[k] c).state (((stepU)^[k] c).tape
        ((stepU)^[k] c).head)).2.2 = .up ∧ N ≤ ((stepU)^[k] c).head + 1) := by
      have := hk k (by omega); omega
    simp only [stepB, ite_eq_right hx]

end UND.MachineP
