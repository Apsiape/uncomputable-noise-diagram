/-
# Lemma 4.1(b): which computation a board carries (M3)

Node M3 of `BLUEPRINT.md` (Part A.4), NEW. Assembles `Machine/Scan.lean` and
`Machine/Passes.lean`.

Paper (Lemma 4.1): "If the initial zero of `h_in` has index `j_*`, `P` can begin simulating `U`
only if its parity bit is one and `j_* + 2 = 2^e` with `e > n₀ + 1`. It then runs exactly
`U(e - n₀ - 1)`." Proof, last sentences: "Only RUN can enter HALT, and it executes `U` on that
unary input. Any shortage of tape during any routine fails."

Formalized in the form Prop 4.3 consumes (Lemma 4.2 forces `j_* + 2 = 2^{a+1}` on every large
board, so the clause "any other positive count eventually fails" is not needed and is not
formalized; see `STATUS.md`, D29):
* `Decodes e h π`: ones of `h_in` below `j_* = 2^e - 2`, a zero with parity bit one at `j_*`;
* **`decode_halts`**: if `U` halts on `e - n₀ - 1` (`e ≥ n₀ + 2`), the unbounded run reaches HALT
  at one time `T`, the same for every input tracks above `j_*`;
* **`decode_no_halt`**: if `U` does not halt on `e - n₀ - 1`, the run never enters HALT;
* **`guard_no_halt`**: if the first zero of `h_in` has parity bit zero, or there is no zero, the
  run never enters HALT (the parity guard);
* on the board (`N` cells, Lemma 4.1(a)): **`runP_no_halt`** (no HALT in the unbounded run ⇒ no
  board content carries HALT) and **`runP_halts`** (HALT at time `T < N` ⇒ the board column `T`
  carries HALT).
-/
import UncomputableNoiseDiagram.Machine.Passes

set_option autoImplicit false

namespace UND.MachineP

open UPD

variable {U : Machine} {n0 : ℕ}

/-- The input tracks of a decoding board: `h_in = 1` below `j_* = 2^e - 2`, `h_in = 0` and
`π = 1` at `j_*`. -/
def Decodes (e : ℕ) (h pi : ℕ → Bool) : Prop :=
  (∀ j < 2 ^ e - 2, h j = true) ∧ h (2 ^ e - 2) = false ∧ pi (2 ^ e - 2) = true

theorem forgetC_tape1 (h pi : ℕ → Bool) (js k : ℕ) (q : PState U n0) :
    forgetC (⟨tape1 U h pi js, k, q⟩ : PCfg U n0) = ⟨F1 U js, k, q⟩ := by
  show (⟨fun j => forgetT (tape1 U h pi js j), k, q⟩ : PCfg U n0) = _
  rw [forget_tape1]

/-- After SCAN the run's states do not depend on the input tracks: they are those of the fixed
run from PLUS on the forgotten tape `F1`. -/
theorem forget_scan (e : ℕ) (h pi : ℕ → Bool) (hd : Decodes e h pi) (k : ℕ) :
    ((stepU)^[2 ^ e - 2 + 1 + k] (cfg0 U n0 h pi)).state =
      ((stepU)^[k] (⟨F1 U (2 ^ e - 2), 2 ^ e - 2 + 1, .plus⟩ : PCfg U n0)).state := by
  rw [show 2 ^ e - 2 + 1 + k = k + (2 ^ e - 2 + 1) by ring, Function.iterate_add_apply,
    scan_plus h pi _ hd.1 hd.2.1 hd.2.2,
    ← state_iterate_forget (⟨tape1 U h pi (2 ^ e - 2), 2 ^ e - 2 + 1, .plus⟩ : PCfg U n0)
      (by simp) k, forgetC_tape1]

/-- **Lemma 4.1(b), the halting case**: if `j_* + 2 = 2^e`, `e ≥ n₀ + 2`, the parity bit at the
initial zero is one and `U` halts on `e - n₀ - 1`, the run of `P` reaches HALT at one time `T`,
whatever the input tracks above `j_*`. -/
theorem decode_halts (e : ℕ) (he : n0 + 2 ≤ e) (hU : U.HaltsOn (e - n0 - 1)) :
    ∃ T, ∀ h pi : ℕ → Bool, Decodes e h pi →
      ((stepU)^[T] (cfg0 U n0 h pi)).state = .halt := by
  obtain ⟨k0, hk0⟩ := reaches_run (U := U) (n0 := n0) e he
  obtain ⟨k1, hk1⟩ := sim_halts (n0 := n0) (2 ^ e) (marks (2 ^ e) (e + 1)) (finTok e) _ hU
  refine ⟨2 ^ e - 2 + 1 + (k1 + k0), fun h pi hd => ?_⟩
  rw [forget_scan e h pi hd, Function.iterate_add_apply, hk0]
  exact hk1

/-- **Lemma 4.1(b), the nonhalting case**: under the same input conditions, if `U` does not halt on
`e - n₀ - 1`, the run of `P` never enters HALT. -/
theorem decode_no_halt (e : ℕ) (he : n0 + 2 ≤ e) (hU : ¬ U.HaltsOn (e - n0 - 1))
    (h pi : ℕ → Bool) (hd : Decodes e h pi) (i : ℕ) :
    ((stepU)^[i] (cfg0 U n0 h pi)).state ≠ .halt := by
  obtain ⟨k0, hk0⟩ := reaches_run (U := U) (n0 := n0) e he
  have hF : ∀ m, ((stepU)^[m] (⟨F1 U (2 ^ e - 2), 2 ^ e - 2 + 1, .plus⟩ : PCfg U n0)).state ≠
      .halt := by
    intro m
    rcases le_total m k0 with hm | hm
    · refine not_halt_before _ ?_ hm
      rw [hk0]; simp [sim]
    · rw [show m = (m - k0) + k0 by omega, Function.iterate_add_apply, hk0]
      exact sim_no_halt _ _ _ _ hU _
  rcases le_total i (2 ^ e - 2 + 1) with hi | hi
  · refine not_halt_before _ ?_ hi
    rw [scan_plus h pi _ hd.1 hd.2.1 hd.2.2]; simp
  · rw [show i = 2 ^ e - 2 + 1 + (i - (2 ^ e - 2 + 1)) by omega, forget_scan e h pi hd]
    exact hF _

/-- **Lemma 4.1(b), the parity guard**: if the first zero of `h_in` has parity bit zero, or `h_in`
has no zero, the run never enters HALT. -/
theorem guard_no_halt (h pi : ℕ → Bool)
    (hg : ∀ j, h j = false → (∀ j' < j, h j' = true) → pi j = false) (i : ℕ) :
    ((stepU)^[i] (cfg0 U n0 h pi)).state ≠ .halt := by
  classical
  by_cases hz : ∃ j, h j = false
  · have h0 : h (Nat.find hz) = false := Nat.find_spec hz
    have hlt : ∀ j < Nat.find hz, h j = true := fun j hj => by
      have := Nat.find_min hz hj
      simpa using this
    exact scan_guard h pi (Nat.find hz) hlt h0 (hg _ h0 hlt) i
  · push Not at hz
    exact scan_forever h pi (fun j => by simpa using hz j) i

/-! ## On the board -/

/-- **No HALT on the board**: if the unbounded run never enters HALT, no content of the board run
on `N` cells carries HALT. -/
theorem runP_no_halt {N : ℕ} (hN : 1 ≤ N) (h pi : ℕ → Bool)
    (hno : ∀ i, ((stepU)^[i] (cfg0 U n0 h pi)).state ≠ .halt) (i : ℕ) (j : Fin N) :
    CarriesHalt U n0 (runP U n0 N h pi i j) = false := by
  rw [runP_eq U n0 hN h pi i]
  simp only [CarriesHalt, colOf]
  split_ifs with hj
  · rw [decide_eq_false_iff_not]
    intro hs
    have hs' := Option.some.inj hs
    rcases stepB_iterate N (cfg0 U n0 h pi) i with he | hf
    · exact hno i (by rw [← he]; exact hs')
    · rw [hf] at hs'; exact absurd hs' (by simp)
  · simp

/-- **HALT on the board**: if the unbounded run is in HALT at time `T < N`, the board column `T`
on `N` cells carries HALT (the head never leaves the tape before, since it is at most at cell `k`
at time `k`). -/
theorem runP_halts {N : ℕ} (h pi : ℕ → Bool) {T : ℕ}
    (hT : ((stepU)^[T] (cfg0 U n0 h pi)).state = .halt) (hTN : T < N) :
    ∃ j : Fin N, CarriesHalt U n0 (runP U n0 N h pi T j) = true := by
  have hhead : ∀ k, ((stepU)^[k] (cfg0 U n0 h pi)).head ≤ k := fun k => by
    have := head_iterate_le (cfg0 U n0 h pi) k
    simpa [cfg0] using this
  have heq := stepB_iterate_eq N (cfg0 U n0 h pi) T (fun k' hk' => by have := hhead k'; omega)
  refine ⟨⟨((stepU)^[T] (cfg0 U n0 h pi)).head, by have := hhead T; omega⟩, ?_⟩
  rw [runP_eq U n0 (by omega) h pi T, heq]
  simp [CarriesHalt, colOf, hT]

/-! ## The read-only tracks -/

/-- No clause of `P` writes `h_in` or `π`. -/
theorem program_tracks (q : PState U n0) (g : Tape U) (r : PState U n0 × Tape U × Mv)
    (h : program U n0 q g = some r) : r.2.1.hin = g.hin ∧ r.2.1.pi = g.pi := by
  obtain ⟨hin, pi, z, p, e, n, u⟩ := g
  cases q <;> simp only [program] at h <;> (try split_ifs at h) <;>
    (obtain rfl := Option.some.inj h; exact ⟨rfl, rfl⟩)

theorem deltaP_tracks (q : PState U n0) (g : Tape U) :
    (deltaP U n0 q g).2.1.hin = g.hin ∧ (deltaP U n0 q g).2.1.pi = g.pi := by
  unfold deltaP
  rcases h : program U n0 q g with _ | r
  · exact ⟨rfl, rfl⟩
  · exact program_tracks q g r h

theorem update_tracks (t : ℕ → Tape U) (h : ℕ) (q : PState U n0) (j : ℕ) :
    (Function.update t h (deltaP U n0 q (t h)).2.1 j).hin = (t j).hin ∧
      (Function.update t h (deltaP U n0 q (t h)).2.1 j).pi = (t j).pi := by
  by_cases hj : j = h
  · subst hj
    rw [Function.update_self]
    exact deltaP_tracks q (t j)
  · rw [Function.update_of_ne hj]
    exact ⟨rfl, rfl⟩

theorem stepB_tracks (N : ℕ) (c : PCfg U n0) (j : ℕ) :
    ((stepB N c).tape j).hin = (c.tape j).hin ∧ ((stepB N c).tape j).pi = (c.tape j).pi := by
  obtain ⟨t, h, q⟩ := c
  simp only [stepB, stepU]
  split <;> (try split) <;> (try split) <;> exact update_tracks t h q j

/-- **The read-only tracks are never written**: every content of the board run carries the input
tracks it was initialized with (the last two clauses of the tableau (10)). -/
theorem runP_tracks {N : ℕ} (hN : 1 ≤ N) (h pi : ℕ → Bool) (i : ℕ) (j : Fin N) :
    (runP U n0 N h pi i j).1.hin = h j ∧ (runP U n0 N h pi i j).1.pi = pi j := by
  rw [runP_eq U n0 hN h pi i]
  simp only [colOf]
  induction i with
  | zero => exact ⟨rfl, rfl⟩
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    obtain ⟨h1, h2⟩ := stepB_tracks N ((stepB N)^[i] (cfg0 U n0 h pi)) j
    exact ⟨h1.trans ih.1, h2.trans ih.2⟩

end UND.MachineP
