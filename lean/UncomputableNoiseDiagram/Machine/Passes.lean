/-
# Lemma 4.1(b), second part: halving passes, SKIP, FINDN/APPENDU (M3)

Part of node M3 of `BLUEPRINT.md` (Part A.4), NEW (template: the hard-model core's label passes,
`UndecidablePhaseDiagram/Background/Run.lean`, `pass_scan`).

Paper (proof of Lemma 4.1): "The scan makes exactly `j_* + 2` marks, with `e_*` on the next cell.
Each `R` pass keeps the odd-numbered surviving marks. Its `c` records their original count capped at
two, and `b` its parity. The ordered termination clauses accept a singleton before rejecting an odd
number exceeding one. Consequently an original power `2^e` has exactly `e` successful even passes
… APPENDN therefore writes `e` tokens. SKIP consumes `n₀ + 1` of them and requires a further token.
FINDN and APPENDU copy precisely the remaining `e - n₀ - 1` tokens to the initially blank `u_*`
track."

Everything here runs after SCAN, on the work tape `wt` (input tracks erased; see `iterate_forget`),
with `M = j_* + 2 = 2^e` marks and the end mark `e_*` at cell `M`:
* `plus_phase`: PLUS and SETEND, then the return: `R_{00}` at cell `0` with marks on `[0, M)`;
* `pass_block`, `pass_blocks`: a pass over blocks of length `2^t`, each starting with a mark,
  keeps the marks of even block index (`marks M t → marks M (t+1)`);
* **`halving_step`** (`t < e`: an even pass, APPENDN writes one more token), **`halving_all`**,
  **`halving_last`** (the singleton pass: `SKIP_0`);
* **`skip_phase`** (`SKIP_c` turns `n₀ + 1` tokens into twos; a further token is required);
* **`copy_step`**, **`copy_all`**, **`copy_last`** (FINDN/APPENDU copy the remaining tokens to
  `u_*`; then `RUN_{q_{U,0}}` at cell `0`);
* **`reaches_run`**: from PLUS at cell `M - 1` (the end of SCAN) the run reaches the simulation
  configuration of `U` on the input `e - n₀ - 1`.
-/
import UncomputableNoiseDiagram.Machine.Scan

set_option autoImplicit false

namespace UND.MachineP

open UPD

variable {U : Machine} {n0 : ℕ}

/-! ## The transitions used after SCAN -/

theorem deltaP_plus (g : Tape U) : deltaP U n0 .plus g = (.setend, { g with p := true }, .up) := by
  simp [deltaP, program]

theorem deltaP_setend (g : Tape U) :
    deltaP U n0 .setend g = (.ret .r00, { g with e := true }, .down) := by
  simp [deltaP, program]

theorem deltaP_r_skip (b : Bool) (c : Fin 3) (g : Tape U) (he : g.e = false) (hp : g.p = false) :
    deltaP U n0 (.r b c) g = (.r b c, g, .up) := by
  simp [deltaP, program, he, hp]

theorem deltaP_r_mark (b : Bool) (c : Fin 3) (g : Tape U) (he : g.e = false) (hp : g.p = true) :
    deltaP U n0 (.r b c) g =
      (.r (!b) ⟨min (c.val + 1) 2, by omega⟩, { g with p := !b }, .up) := by
  simp [deltaP, program, he, hp]

theorem deltaP_r_even (g : Tape U) (he : g.e = true) :
    deltaP U n0 (.r false 2) g = (.ret .appendN, g, .stay) := by
  simp [deltaP, program, he]

theorem deltaP_r_one (g : Tape U) (he : g.e = true) :
    deltaP U n0 (.r true 1) g = (.ret .skip0, g, .stay) := by
  simp [deltaP, program, he]

theorem deltaP_appendN_one (g : Tape U) (hn : g.n = 1) : deltaP U n0 .appendN g = (.appendN, g, .up) := by
  simp [deltaP, program, hn]

theorem deltaP_appendN_zero (g : Tape U) (hn : g.n = 0) :
    deltaP U n0 .appendN g = (.ret .r00, { g with n := 1 }, .stay) := by
  simp [deltaP, program, hn]

theorem deltaP_skip_lt (c : Fin (n0 + 2)) (hc : c.val < n0 + 1) (g : Tape U) (hn : g.n = 1) :
    deltaP U n0 (.skip c) g = (.skip ⟨c.val + 1, by omega⟩, { g with n := 2 }, .up) := by
  simp [deltaP, program, hn, hc]

theorem deltaP_skip_last (c : Fin (n0 + 2)) (hc : c.val = n0 + 1) (g : Tape U) (hn : g.n = 1) :
    deltaP U n0 (.skip c) g = (.ret .findN, g, .stay) := by
  simp [deltaP, program, hn, hc]

theorem deltaP_findN_two (g : Tape U) (hn : g.n = 2) : deltaP U n0 .findN g = (.findN, g, .up) := by
  simp [deltaP, program, hn]

theorem deltaP_findN_one (g : Tape U) (hn : g.n = 1) :
    deltaP U n0 .findN g = (.ret .appendU, { g with n := 2 }, .stay) := by
  simp [deltaP, program, hn]

theorem deltaP_findN_zero (g : Tape U) (hn : g.n = 0) :
    deltaP U n0 .findN g = (.ret .run0, g, .stay) := by
  simp [deltaP, program, hn]

theorem deltaP_appendU_one (g : Tape U) (hu : g.u = 1) : deltaP U n0 .appendU g = (.appendU, g, .up) := by
  simp [deltaP, program, hu]

theorem deltaP_appendU_zero (g : Tape U) (hu : g.u = 0) :
    deltaP U n0 .appendU g = (.ret .findN, { g with u := 1 }, .stay) := by
  simp [deltaP, program, hu]

/-! ## The work tape -/

theorem update_wt_p (M : ℕ) (P : ℕ → Bool) (N : ℕ → Fin 3) (V : ℕ → U.Symbol) (h : ℕ) (x : Bool) :
    Function.update (wt U M P N V) h { wt U M P N V h with p := x } =
      wt U M (Function.update P h x) N V := by
  funext j
  by_cases hj : j = h
  · subst hj; simp [wt]
  · simp [wt, Function.update_of_ne hj]

theorem update_wt_n (M : ℕ) (P : ℕ → Bool) (N : ℕ → Fin 3) (V : ℕ → U.Symbol) (h : ℕ)
    (x : Fin 3) :
    Function.update (wt U M P N V) h { wt U M P N V h with n := x } =
      wt U M P (Function.update N h x) V := by
  funext j
  by_cases hj : j = h
  · subst hj; simp [wt]
  · simp [wt, Function.update_of_ne hj]

/-- Moving up from cell `0` over `k` cells in a fixed state without writing. -/
theorem reach_up (X : PState U n0) (t : ℕ → Tape U) (k : ℕ)
    (hX : ∀ j, j < k → deltaP U n0 X (t j) = (X, t j, .up)) :
    Reaches (⟨t, 0, X⟩ : PCfg U n0) ⟨t, k, X⟩ :=
  ⟨k, by simpa using move_up X t 0 k (fun j _ h2 => hX j (by omega))⟩

theorem ret_home_wt (c : Cont) (M : ℕ) (P : ℕ → Bool) (N : ℕ → Fin 3) (V : ℕ → U.Symbol)
    (k : ℕ) : Reaches (⟨wt U M P N V, k, .ret c⟩ : PCfg U n0) ⟨wt U M P N V, 0, c.state⟩ :=
  ⟨k + 1, ret_home c _ (fun j => wt_z M P N V j) k⟩

/-! ## PLUS and SETEND -/

/-- The forgotten tape at the end of SCAN: `z = [j = 0]`, `p_* = [j ≤ j_*]`. -/
def F1 (U : Machine) (js : ℕ) : ℕ → Tape U :=
  fun j => ⟨false, false, decide (j = 0), decide (j ≤ js), false, 0, 0⟩

theorem forget_tape1 (h pi : ℕ → Bool) (js : ℕ) :
    (fun j => forgetT (tape1 U h pi js j)) = F1 U js := by
  funext j
  by_cases hj : j ≤ js <;> simp [tape1, tape0, forgetT, F1, hj]

/-- The blank `u_*` track and the empty token track. -/
def V0 (U : Machine) : ℕ → U.Symbol := fun _ => 0

/-- `t` tokens `n_* = 1` on the cells `0, …, t - 1`. -/
def toks (t : ℕ) : ℕ → Fin 3 := fun j => if j < t then 1 else 0

/-- The marks surviving `t` halving passes: the multiples of `2^t` below `M`. -/
def marks (M t : ℕ) (j : ℕ) : Bool := decide (j < M ∧ 2 ^ t ∣ j)

/-- **PLUS and SETEND**: the last two marks and the end mark, then the return to `R_{00}`. -/
theorem plus_phase (js : ℕ) :
    Reaches (⟨F1 U js, js + 1, .plus⟩ : PCfg U n0)
      ⟨wt U (js + 2) (marks (js + 2) 0) (toks 0) (V0 U), 0, .r false 0⟩ := by
  have e1 : Function.update (Function.update (F1 U js) (js + 1) { F1 U js (js + 1) with p := true })
      (js + 2) { Function.update (F1 U js) (js + 1) { F1 U js (js + 1) with p := true } (js + 2) with
        e := true } = wt U (js + 2) (marks (js + 2) 0) (toks 0) (V0 U) := by
    funext j
    by_cases h1 : j = js + 2
    · subst h1; simp [F1, wt, marks, toks, V0]
    · rw [Function.update_of_ne h1]
      by_cases h2 : j = js + 1
      · subst h2; simp [F1, wt, marks, toks, V0]
      · rw [Function.update_of_ne h2]
        simp only [F1, wt, marks, toks, V0, pow_zero, one_dvd, and_true]
        congr 1 <;> simp <;> omega
  refine (Reaches.step (stepU_up (deltaP_plus _))).trans ?_
  refine (Reaches.step (stepU_down (deltaP_setend _) (by omega))).trans ?_
  rw [show js + 1 + 1 - 1 = js + 1 by omega, show js + 1 + 1 = js + 2 by omega, e1]
  exact ret_home_wt .r00 _ _ _ _ _

/-! ## A halving pass -/

/-- **One block of a pass**: a mark at `a` followed by `s - 1` unmarked cells (all before the end
mark): the mark is kept (`b = 0`) or erased (`b = 1`), `b` flips and `c` counts up to two. -/
theorem pass_block (M : ℕ) (P : ℕ → Bool) (N : ℕ → Fin 3) (V : ℕ → U.Symbol) (a s : ℕ)
    (hs : 1 ≤ s) (haM : a + s ≤ M) (hPa : P a = true)
    (hP : ∀ j, a < j → j < a + s → P j = false) (b : Bool) (c : Fin 3) :
    (stepU)^[s] (⟨wt U M P N V, a, .r b c⟩ : PCfg U n0) =
      ⟨wt U M (Function.update P a (!b)) N V, a + s,
        .r (!b) ⟨min (c.val + 1) 2, by omega⟩⟩ := by
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + 1 := ⟨s - 1, by omega⟩
  rw [Function.iterate_succ_apply]
  have hd : deltaP U n0 (.r b c) (wt U M P N V a) =
      (.r (!b) ⟨min (c.val + 1) 2, by omega⟩, { wt U M P N V a with p := !b }, .up) :=
    deltaP_r_mark _ _ _ (by simp [wt]; omega) (by simp [wt, hPa])
  rw [stepU_up hd, update_wt_p,
    move_up _ _ (a + 1) s' (fun j h1 h2 => deltaP_r_skip _ _ _ (by simp [wt]; omega)
      (by simp [wt, Function.update_of_ne (show j ≠ a by omega), hP j (by omega) (by omega)])),
    show a + 1 + s' = a + (s' + 1) by omega]

/-- The marks during the pass `t`: blocks before `i` already halved. -/
def passP (M t i : ℕ) (j : ℕ) : Bool := if j < i * 2 ^ t then marks M (t + 1) j else marks M t j

/-- The state after `i` blocks of a pass from `R_{00}`. -/
def rstate (n0 : ℕ) (i : ℕ) : PState U n0 := .r (decide (i % 2 = 1)) ⟨min i 2, by omega⟩

theorem not_dvd_between {t i j : ℕ} (h1 : i * 2 ^ t < j) (h2 : j < (i + 1) * 2 ^ t) :
    ¬ 2 ^ t ∣ j := by
  rintro ⟨m, rfl⟩
  have hp : 0 < 2 ^ t := by positivity
  have a1 : i < m := Nat.lt_of_mul_lt_mul_left (a := 2 ^ t) (by linarith [mul_comm i (2 ^ t)])
  have a2 : m < i + 1 := Nat.lt_of_mul_lt_mul_left (a := 2 ^ t) (by linarith [mul_comm (i + 1) (2 ^ t)])
  omega

theorem passP_succ (M t i : ℕ) (hi : (i + 1) * 2 ^ t ≤ M) :
    Function.update (passP M t i) (i * 2 ^ t) (!decide (i % 2 = 1)) = passP M t (i + 1) := by
  have hp : 0 < 2 ^ t := by positivity
  have hlt : i * 2 ^ t < (i + 1) * 2 ^ t := by nlinarith
  funext j
  by_cases hj : j = i * 2 ^ t
  · subst hj
    rw [Function.update_self]
    simp only [passP, marks, ite_eq_left hlt]
    have h2 : 2 ^ (t + 1) ∣ i * 2 ^ t ↔ 2 ∣ i := by
      rw [pow_succ, mul_comm (2 ^ t) 2]
      exact Nat.mul_dvd_mul_iff_right hp
    rw [Bool.eq_iff_iff]
    simp only [Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq, h2]
    constructor
    · intro h; exact ⟨by omega, by omega⟩
    · rintro ⟨-, h⟩; omega
  · rw [Function.update_of_ne hj]
    simp only [passP]
    by_cases h1 : j < i * 2 ^ t
    · rw [ite_eq_left h1, ite_eq_left (by omega)]
    · rw [ite_eq_right h1]
      by_cases h3 : j < (i + 1) * 2 ^ t
      · rw [ite_eq_left h3]
        have hnd := not_dvd_between (show i * 2 ^ t < j by omega) h3
        have hnd' : ¬ 2 ^ (t + 1) ∣ j := fun h => hnd (dvd_trans (pow_dvd_pow 2 (by omega)) h)
        simp [marks, hnd, hnd']
      · rw [ite_eq_right h3]

/-- **A pass over `K` blocks of length `2^t`** (`K·2^t = M`), from `R_{00}` at cell `0` on the
marks `marks M t`: after `i` blocks the head is at `i·2^t` in `R_{(i mod 2), min(i,2)}`. -/
theorem pass_blocks (M t K : ℕ) (hK : K * 2 ^ t = M) (N : ℕ → Fin 3) (V : ℕ → U.Symbol) (i : ℕ)
    (hi : i ≤ K) :
    Reaches (⟨wt U M (marks M t) N V, 0, .r false 0⟩ : PCfg U n0)
      ⟨wt U M (passP M t i) N V, i * 2 ^ t, rstate n0 i⟩ := by
  induction i with
  | zero =>
    have h1 : passP M t 0 = marks M t := by funext j; simp [passP]
    rw [h1, zero_mul]
    exact Reaches.refl _
  | succ i ih =>
    have hp : 0 < 2 ^ t := by positivity
    have hiK : (i + 1) * 2 ^ t ≤ M := by rw [← hK]; exact Nat.mul_le_mul_right _ hi
    refine (ih (by omega)).trans (Reaches.of_iterate (2 ^ t) ?_)
    have hPa : passP M t i (i * 2 ^ t) = true := by
      have : i * 2 ^ t < M := by nlinarith
      simp [passP, marks, this]
    have hP : ∀ j, i * 2 ^ t < j → j < i * 2 ^ t + 2 ^ t → passP M t i j = false := by
      intro j h1 h2
      have hnd := not_dvd_between h1 (by nlinarith)
      simp [passP, show ¬ j < i * 2 ^ t by omega, marks, hnd]
    rw [rstate, pass_block M (passP M t i) N V (i * 2 ^ t) (2 ^ t) hp (by nlinarith) hPa hP,
      passP_succ M t i hiK, show i * 2 ^ t + 2 ^ t = (i + 1) * 2 ^ t by ring]
    congr 1
    simp only [rstate]
    congr 1
    · rcases Nat.mod_two_eq_zero_or_one i with h | h
      · rw [h, show (i + 1) % 2 = 1 by omega]; rfl
      · rw [h, show (i + 1) % 2 = 0 by omega]; rfl
    · exact Fin.ext (by simp only; omega)

theorem passP_end (M t K : ℕ) (hK : K * 2 ^ t = M) : passP M t K = marks M (t + 1) := by
  funext j
  simp only [passP, hK]
  by_cases h : j < M
  · rw [ite_eq_left h]
  · rw [ite_eq_right h]
    simp [marks, h]

theorem two_pow_split {e t : ℕ} (ht : t ≤ e) : 2 ^ (e - t) * 2 ^ t = 2 ^ e := by
  rw [← pow_add, Nat.sub_add_cancel ht]

/-- **An even halving pass and APPENDN** (`t < e`, `M = 2^e`): the marks `marks M t` become
`marks M (t+1)` and one more token is appended; back to `R_{00}` at cell `0`. -/
theorem halving_step (e t : ℕ) (ht : t < e) :
    Reaches (⟨wt U (2 ^ e) (marks (2 ^ e) t) (toks t) (V0 U), 0, .r false 0⟩ : PCfg U n0)
      ⟨wt U (2 ^ e) (marks (2 ^ e) (t + 1)) (toks (t + 1)) (V0 U), 0, .r false 0⟩ := by
  set M := 2 ^ e with hM
  have hK := two_pow_split ht.le
  rw [← hM] at hK
  have hKeven : 2 ^ (e - t) % 2 = 0 := by
    obtain ⟨s, hs⟩ : ∃ s, e - t = s + 1 := ⟨e - t - 1, by omega⟩
    rw [hs, pow_succ]; omega
  have hK2 : 2 ≤ 2 ^ (e - t) := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ (e - t) := Nat.pow_le_pow_right (by norm_num) (by omega)
  refine (pass_blocks M t (2 ^ (e - t)) hK (toks t) (V0 U) (2 ^ (e - t)) le_rfl).trans ?_
  rw [passP_end M t _ hK, hK]
  have hst : rstate n0 (2 ^ (e - t)) = (.r false 2 : PState U n0) := by
    simp only [rstate, hKeven]
    congr 1
    apply Fin.ext
    simp only
    omega
  rw [hst]
  -- the end mark: `R_{0,2}` returns with continuation APPENDN
  refine (Reaches.step (stepU_stay (deltaP_r_even _ (by simp [wt])))).trans ?_
  rw [Function.update_eq_self]
  refine (ret_home_wt .appendN _ _ _ _ M).trans ?_
  -- APPENDN over the `t` tokens, then one more
  refine (reach_up PState.appendN (wt U M (marks M (t + 1)) (toks t) (V0 U)) t
    (fun j h2 => deltaP_appendN_one _ (by simp [wt, toks]; omega))).trans ?_
  refine (Reaches.step (stepU_stay (deltaP_appendN_zero _ (by simp [wt, toks])))).trans ?_
  rw [update_wt_n]
  have htoks : Function.update (toks t) t (1 : Fin 3) = toks (t + 1) := by
    funext j
    by_cases hj : j = t
    · subst hj; simp [toks]
    · rw [Function.update_of_ne hj]
      simp only [toks]
      by_cases h : j < t
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega)]
  rw [htoks]
  exact ret_home_wt .r00 _ _ _ _ t

/-- **`e` even passes**: from the `2^e` marks of SCAN, `e` halving passes leave the single mark at
cell `0` and `e` tokens. -/
theorem halving_all (e : ℕ) (t : ℕ) (ht : t ≤ e) :
    Reaches (⟨wt U (2 ^ e) (marks (2 ^ e) 0) (toks 0) (V0 U), 0, .r false 0⟩ : PCfg U n0)
      ⟨wt U (2 ^ e) (marks (2 ^ e) t) (toks t) (V0 U), 0, .r false 0⟩ := by
  induction t with
  | zero => exact Reaches.refl _
  | succ t ih => exact (ih (by omega)).trans (halving_step e t (by omega))

/-- **The singleton pass**: one mark left, the pass ends in `R_{1,1}` and returns with
continuation `SKIP_0`. -/
theorem halving_last (e : ℕ) :
    Reaches (⟨wt U (2 ^ e) (marks (2 ^ e) e) (toks e) (V0 U), 0, .r false 0⟩ : PCfg U n0)
      ⟨wt U (2 ^ e) (marks (2 ^ e) (e + 1)) (toks e) (V0 U), 0, .skip 0⟩ := by
  set M := 2 ^ e with hM
  have hK : 1 * 2 ^ e = M := by rw [one_mul]
  refine (pass_blocks M e 1 hK (toks e) (V0 U) 1 le_rfl).trans ?_
  rw [passP_end M e 1 hK, hK]
  have hst : rstate n0 1 = (.r true 1 : PState U n0) := rfl
  rw [hst]
  refine (Reaches.step (stepU_stay (deltaP_r_one _ (by simp [wt])))).trans ?_
  rw [Function.update_eq_self]
  exact ret_home_wt .skip0 _ _ _ _ M

/-! ## SKIP -/

/-- The tokens during SKIP: twos below `c`. -/
def skTok (e c : ℕ) : ℕ → Fin 3 := fun j => if j < c then 2 else toks e j

theorem skip_loop (M : ℕ) (P : ℕ → Bool) (e : ℕ) (he : n0 + 2 ≤ e) (c : ℕ) (hc : c ≤ n0 + 1) :
    (stepU)^[c] (⟨wt U M P (toks e) (V0 U), 0, .skip 0⟩ : PCfg U n0) =
      ⟨wt U M P (skTok e c) (V0 U), c, .skip ⟨c, by omega⟩⟩ := by
  induction c with
  | zero =>
    have : skTok e 0 = toks e := by funext j; simp [skTok]
    rw [this]; rfl
  | succ c ih =>
    rw [Function.iterate_succ_apply', ih (by omega)]
    have hd := deltaP_skip_lt (n0 := n0) ⟨c, by omega⟩ (by simp only; omega)
      (wt U M P (skTok e c) (V0 U) c) (by simp [wt, skTok, toks]; omega)
    rw [stepU_up hd, update_wt_n]
    congr 2
    funext j
    by_cases hj : j = c
    · subst hj; simp [skTok]
    · rw [Function.update_of_ne hj]
      simp only [skTok]
      by_cases h : j < c
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega)]

/-- **SKIP** (`e ≥ n₀ + 2`): `n₀ + 1` tokens become twos, a further token is present; FINDN at
cell `0`. -/
theorem skip_phase (M : ℕ) (P : ℕ → Bool) (e : ℕ) (he : n0 + 2 ≤ e) :
    Reaches (⟨wt U M P (toks e) (V0 U), 0, .skip 0⟩ : PCfg U n0)
      ⟨wt U M P (skTok e (n0 + 1)) (V0 U), 0, .findN⟩ := by
  refine (Reaches.of_iterate _ (skip_loop M P e he (n0 + 1) le_rfl)).trans ?_
  have hd := deltaP_skip_last (n0 := n0) ⟨n0 + 1, by omega⟩ rfl
    (wt U M P (skTok e (n0 + 1)) (V0 U) (n0 + 1)) (by simp [wt, skTok, toks]; omega)
  refine (Reaches.step (stepU_stay hd)).trans ?_
  rw [Function.update_eq_self]
  exact ret_home_wt .findN _ _ _ _ _

/-! ## FINDN and APPENDU -/

/-- The tokens after `i` copies: twos below `n₀ + 1 + i`. -/
def fnTok (n0 e i : ℕ) : ℕ → Fin 3 := fun j => if j < n0 + 1 + i then 2 else toks e j

/-- The `u_*` track after `i` copies: `1^i`. -/
def uTape (U : Machine) (i : ℕ) : ℕ → U.Symbol := fun j => if j < i then 1 else 0

theorem update_wt_u' (M : ℕ) (P : ℕ → Bool) (N : ℕ → Fin 3) (V : ℕ → U.Symbol) (h : ℕ)
    (x : U.Symbol) :
    Function.update (wt U M P N V) h { wt U M P N V h with u := x } =
      wt U M P N (Function.update V h x) := update_wt_u M P N V h x

theorem zero_ne_one_sym : (0 : U.Symbol) ≠ 1 := by
  intro h
  have := congrArg Fin.val h
  simp at this

/-- **One copy** (`i < e - n₀ - 1`): FINDN finds the next token, turns it into a two, APPENDU
appends a one to `u_*`; back to FINDN at cell `0`. -/
theorem copy_step (M : ℕ) (P : ℕ → Bool) (e i : ℕ) (hi : n0 + 1 + i < e) :
    Reaches (⟨wt U M P (fnTok n0 e i) (uTape U i), 0, .findN⟩ : PCfg U n0)
      ⟨wt U M P (fnTok n0 e (i + 1)) (uTape U (i + 1)), 0, .findN⟩ := by
  -- FINDN over the twos
  refine (reach_up PState.findN (wt U M P (fnTok n0 e i) (uTape U i)) (n0 + 1 + i)
    (fun j h2 => deltaP_findN_two _ (by simp [wt, fnTok]; omega))).trans ?_
  refine (Reaches.step (stepU_stay (deltaP_findN_one _
    (by simp [wt, fnTok, toks]; omega)))).trans ?_
  rw [update_wt_n]
  have hN : Function.update (fnTok n0 e i) (n0 + 1 + i) (2 : Fin 3) = fnTok n0 e (i + 1) := by
    funext j
    by_cases hj : j = n0 + 1 + i
    · subst hj; simp [fnTok]
    · rw [Function.update_of_ne hj]
      simp only [fnTok]
      by_cases h : j < n0 + 1 + i
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega)]
  rw [hN]
  refine (ret_home_wt .appendU _ _ _ _ _).trans ?_
  -- APPENDU over the `i` ones of `u_*`
  refine (reach_up PState.appendU (wt U M P (fnTok n0 e (i + 1)) (uTape U i)) i
    (fun j h2 => deltaP_appendU_one _ (by simp [wt, uTape]; omega))).trans ?_
  refine (Reaches.step (stepU_stay (deltaP_appendU_zero _ (by simp [wt, uTape])))).trans ?_
  rw [update_wt_u']
  have hV : Function.update (uTape U i) i (1 : U.Symbol) = uTape U (i + 1) := by
    funext j
    by_cases hj : j = i
    · subst hj; simp [uTape]
    · rw [Function.update_of_ne hj]
      simp only [uTape]
      by_cases h : j < i
      · rw [ite_eq_left h, ite_eq_left (by omega)]
      · rw [ite_eq_right h, ite_eq_right (by omega)]
  rw [hV]
  exact ret_home_wt .findN _ _ _ _ _

theorem copy_all (M : ℕ) (P : ℕ → Bool) (e i : ℕ) (hi : n0 + 1 + i ≤ e) :
    Reaches (⟨wt U M P (fnTok n0 e 0) (uTape U 0), 0, .findN⟩ : PCfg U n0)
      ⟨wt U M P (fnTok n0 e i) (uTape U i), 0, .findN⟩ := by
  induction i with
  | zero => exact Reaches.refl _
  | succ i ih => exact (ih (by omega)).trans (copy_step M P e i (by omega))

/-- **The end of the copy**: no token left; RUN in the initial state of `U` at cell `0`. -/
theorem copy_last (M : ℕ) (P : ℕ → Bool) (e : ℕ) (he : n0 + 1 ≤ e) :
    Reaches (⟨wt U M P (fnTok n0 e (e - n0 - 1)) (uTape U (e - n0 - 1)), 0, .findN⟩ :
        PCfg U n0)
      ⟨wt U M P (fnTok n0 e (e - n0 - 1)) (uTape U (e - n0 - 1)), 0, .run 0⟩ := by
  refine (reach_up PState.findN (wt U M P (fnTok n0 e (e - n0 - 1)) (uTape U (e - n0 - 1))) e
    (fun j h2 => deltaP_findN_two _ (by simp [wt, fnTok]; omega))).trans ?_
  refine (Reaches.step (stepU_stay (deltaP_findN_zero _
    (by simp [wt, fnTok, toks]; omega)))).trans ?_
  rw [Function.update_eq_self]
  exact ret_home_wt .run0 _ _ _ _ _

/-! ## From the end of SCAN to RUN -/

/-- The final token track: twos on `[0, e)`. -/
def finTok (e : ℕ) : ℕ → Fin 3 := fun j => if j < e then 2 else 0

theorem fnTok_last (e : ℕ) (he : n0 + 1 ≤ e) : fnTok n0 e (e - n0 - 1) = finTok e := by
  funext j
  simp only [fnTok, finTok, toks]
  by_cases h : j < e
  · rw [ite_eq_left (by omega), ite_eq_left h]
  · rw [ite_eq_right (by omega), ite_eq_right h, ite_eq_right h]

theorem uTape_eq_start (L : ℕ) : uTape U L = (U.start L).tape := rfl

/-- **From PLUS at cell `2^e - 1` (the end of SCAN) to RUN** (`e ≥ n₀ + 2`): the run reaches the
simulation configuration of `U` started on the unary input `e - n₀ - 1`. -/
theorem reaches_run (e : ℕ) (he : n0 + 2 ≤ e) :
    Reaches (⟨F1 U (2 ^ e - 2), 2 ^ e - 2 + 1, .plus⟩ : PCfg U n0)
      (sim (2 ^ e) (marks (2 ^ e) (e + 1)) (finTok e) (U.start (e - n0 - 1))) := by
  have h4 : 4 ≤ 2 ^ e := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hM : 2 ^ e - 2 + 2 = 2 ^ e := by omega
  have h1 := plus_phase (U := U) (n0 := n0) (2 ^ e - 2)
  rw [hM] at h1
  refine h1.trans ((halving_all e e le_rfl).trans ((halving_last e).trans
    ((skip_phase _ _ e he).trans ?_)))
  have hs : skTok e (n0 + 1) = fnTok n0 e 0 := by
    funext j; simp [skTok, fnTok]
  have hv : V0 U = uTape U 0 := by funext j; simp [V0, uTape]
  rw [hs, hv]
  refine (copy_all _ _ e (e - n0 - 1) (by omega)).trans ?_
  refine (copy_last _ _ e (by omega)).trans ?_
  rw [fnTok_last e (by omega)]
  exact Reaches.refl _

end UND.MachineP
