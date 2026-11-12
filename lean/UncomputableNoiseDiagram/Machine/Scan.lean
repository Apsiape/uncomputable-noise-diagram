/-
# Lemma 4.1(b), first part: steps, the SCAN phase, the parity guard, and RUN simulating `U` (M3)

Part of node M3 of `BLUEPRINT.md` (Part A.4), NEW (template: the hard-model core's
`UndecidablePhaseDiagram/Background/Run.lean`: `stepU_up/stay/down`, `scan_up`, `scan_down`).

Paper (Lemma 4.1(b) and its proof): "If the initial zero of `h_in` has index `j_*`, `P` can begin
simulating `U` only if its parity bit is one and `j_* + 2 = 2^e` with `e > n₀ + 1`. It then runs
exactly `U(e - n₀ - 1)`. … The scan makes exactly `j_* + 2` marks, with `e_*` on the next cell. …
Only RUN can enter HALT, and it executes `U` on that unary input."

* `stepU_up`, `stepU_stay`, `stepU_down`, `stepU_down_zero`; `head_le` (a head moves at most one
  cell per step, so at time `i` it is at most at cell `i`);
* `Reaches` (reachability under `stepU`), `move_up`, `move_down`, `scan_up` (fixed-state sweeps),
  `ret_home` (a return to the origin);
* HALT and FAIL are absorbing (`iterate_halt`, `iterate_fail`, `not_halt_before`);
* **forgetting the read-only input tracks**: away from SCAN, `δ_P` neither reads nor writes `h_in`,
  `π` (`program_forget`), so the run commutes with erasing them (`iterate_forget`): after SCAN the
  run is one fixed trajectory, whatever the input tracks beyond the initial zero;
* **the SCAN phase**: `scan_phase` (marks on the cells below the initial zero), `scan_plus` (parity
  bit one: PLUS after `j_* + 1` steps), **`scan_guard`** (parity bit zero: FAIL, never HALT),
  **`scan_forever`** (no zero: SCAN forever, never HALT);
* **RUN simulates `U`** on the `u_*` track: `wt` (the work tape), `sim`, `sim_step`,
  `sim_step_none`, **`sim_inv`**, **`sim_halts`** (if `U` halts on `L` the simulation reaches
  HALT), **`sim_no_halt`** (if not, it never does).
-/
import UncomputableNoiseDiagram.Machine.Run

set_option autoImplicit false

namespace UND.MachineP

open UPD

variable {U : Machine} {n0 : ℕ}

/-! ## Single steps -/

theorem stepU_up {t : ℕ → Tape U} {h : ℕ} {q q' : PState U n0} {g' : Tape U}
    (hd : deltaP U n0 q (t h) = (q', g', .up)) :
    stepU (⟨t, h, q⟩ : PCfg U n0) = ⟨Function.update t h g', h + 1, q'⟩ := by
  simp [stepU, hd]

theorem stepU_stay {t : ℕ → Tape U} {h : ℕ} {q q' : PState U n0} {g' : Tape U}
    (hd : deltaP U n0 q (t h) = (q', g', .stay)) :
    stepU (⟨t, h, q⟩ : PCfg U n0) = ⟨Function.update t h g', h, q'⟩ := by
  simp [stepU, hd]

theorem stepU_down {t : ℕ → Tape U} {h : ℕ} {q q' : PState U n0} {g' : Tape U}
    (hd : deltaP U n0 q (t h) = (q', g', .down)) (h0 : h ≠ 0) :
    stepU (⟨t, h, q⟩ : PCfg U n0) = ⟨Function.update t h g', h - 1, q'⟩ := by
  simp [stepU, hd, h0]

theorem stepU_down_zero {t : ℕ → Tape U} {q q' : PState U n0} {g' : Tape U}
    (hd : deltaP U n0 q (t 0) = (q', g', .down)) :
    stepU (⟨t, 0, q⟩ : PCfg U n0) = ⟨Function.update t 0 g', 0, .fail⟩ := by
  simp [stepU, hd]

/-- A head moves at most one cell per step. -/
theorem head_stepU_le (c : PCfg U n0) : (stepU c).head ≤ c.head + 1 := by
  obtain ⟨t, h, q⟩ := c
  unfold stepU
  split
  · simp
  · simp
  · split
    · simp
    · simp only
      omega

/-- From cell `0`, the head is at most at cell `i` at time `i`. -/
theorem head_iterate_le (c : PCfg U n0) (i : ℕ) : ((stepU)^[i] c).head ≤ c.head + i := by
  induction i with
  | zero => simp
  | succ i ih =>
    rw [Function.iterate_succ_apply']
    have := head_stepU_le ((stepU)^[i] c)
    omega

/-! ## Reachability and sweeps -/

/-- `c'` is reached from `c` by the unbounded run of `P`. -/
def Reaches (c c' : PCfg U n0) : Prop := ∃ k, (stepU)^[k] c = c'

theorem Reaches.refl (c : PCfg U n0) : Reaches c c := ⟨0, rfl⟩

theorem Reaches.trans {c c' c'' : PCfg U n0} (h1 : Reaches c c') (h2 : Reaches c' c'') :
    Reaches c c'' := by
  obtain ⟨k1, rfl⟩ := h1
  obtain ⟨k2, rfl⟩ := h2
  exact ⟨k2 + k1, Function.iterate_add_apply _ _ _ _⟩

theorem Reaches.of_iterate {c c' : PCfg U n0} (k : ℕ) (h : (stepU)^[k] c = c') : Reaches c c' :=
  ⟨k, h⟩

theorem Reaches.step {c c' : PCfg U n0} (h : stepU c = c') : Reaches c c' := ⟨1, h⟩

/-- Moving up in a fixed state `X` without writing, over the cells `a, …, a + k - 1`. -/
theorem move_up (X : PState U n0) (t : ℕ → Tape U) (a k : ℕ)
    (hX : ∀ j, a ≤ j → j < a + k → deltaP U n0 X (t j) = (X, t j, .up)) :
    (stepU)^[k] (⟨t, a, X⟩ : PCfg U n0) = ⟨t, a + k, X⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (fun j h1 h2 => hX j h1 (by omega)),
      stepU_up (hX (a + k) (by omega) (by omega)), Function.update_eq_self]
    rfl

/-- Moving down in a fixed state `X` without writing, from cell `a + k` to cell `a`. -/
theorem move_down (X : PState U n0) (t : ℕ → Tape U) (a k : ℕ)
    (hX : ∀ j, a < j → j ≤ a + k → deltaP U n0 X (t j) = (X, t j, .down)) :
    (stepU)^[k] (⟨t, a + k, X⟩ : PCfg U n0) = ⟨t, a, X⟩ := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, stepU_down (hX (a + (k + 1)) (by omega) le_rfl) (by omega),
      Function.update_eq_self, show a + (k + 1) - 1 = a + k by omega]
    exact ih (fun j h1 h2 => hX j h1 (by omega))

/-- Scanning up in a fixed state `X` over the cells `a, …, a + k - 1`, each satisfying `Q`,
writing `w` on each. -/
theorem scan_up (X : PState U n0) (w : Tape U → Tape U) (Q : Tape U → Prop)
    (hX : ∀ g, Q g → deltaP U n0 X g = (X, w g, .up)) (t : ℕ → Tape U) (a k : ℕ)
    (hQ : ∀ j, a ≤ j → j < a + k → Q (t j)) :
    (stepU)^[k] (⟨t, a, X⟩ : PCfg U n0) =
      ⟨fun j => if a ≤ j ∧ j < a + k then w (t j) else t j, a + k, X⟩ := by
  induction k with
  | zero =>
    have e : (fun j => if a ≤ j ∧ j < a + 0 then w (t j) else t j) = t := by
      funext j; rw [ite_eq_right (by omega)]
    rw [e]; rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply', ih (fun j h1 h2 => hQ j h1 (by omega))]
    have hd : deltaP U n0 X ((fun j => if a ≤ j ∧ j < a + k then w (t j) else t j) (a + k)) =
        (X, w (t (a + k)), .up) := by
      dsimp only
      rw [ite_eq_right (by omega)]
      exact hX _ (hQ (a + k) (by omega) (by omega))
    rw [stepU_up hd]
    congr 1
    funext j
    by_cases hj : j = a + k
    · subst hj
      rw [Function.update_self, ite_eq_left (by omega)]
    · rw [Function.update_of_ne hj]
      by_cases h1 : a ≤ j ∧ j < a + k
      · rw [ite_eq_left h1, ite_eq_left (by omega)]
      · rw [ite_eq_right h1, ite_eq_right (by omega)]

theorem deltaP_ret_z (c : Cont) (g : Tape U) (hz : g.z = true) :
    deltaP U n0 (.ret c) g = (c.state, g, .stay) := by
  simp [deltaP, program, hz]

theorem deltaP_ret (c : Cont) (g : Tape U) (hz : g.z = false) :
    deltaP U n0 (.ret c) g = (.ret c, g, .down) := by
  simp [deltaP, program, hz]

/-- **A return to the origin** from cell `k` (`z = [j = 0]`): `k + 1` steps, ending in the
continuation's state at cell `0`. -/
theorem ret_home (c : Cont) (t : ℕ → Tape U) (ht : ∀ j, (t j).z = decide (j = 0)) (k : ℕ) :
    (stepU)^[k + 1] (⟨t, k, .ret c⟩ : PCfg U n0) = ⟨t, 0, c.state⟩ := by
  have hm := move_down (U := U) (n0 := n0) (.ret c) t 0 k
    (fun j h1 _ => deltaP_ret c _ (by rw [ht]; simp; omega))
  rw [zero_add] at hm
  rw [Function.iterate_succ_apply', hm, stepU_stay (deltaP_ret_z c _ (by rw [ht]; simp)),
    Function.update_eq_self]

/-! ## HALT and FAIL are absorbing -/

theorem stepU_state_halt (c : PCfg U n0) (h : c.state = .halt) : stepU c = c := by
  obtain ⟨t, hh, q⟩ := c
  simp only at h
  subst h
  exact stepU_halt t hh

theorem stepU_state_fail (c : PCfg U n0) (h : c.state = .fail) : stepU c = c := by
  obtain ⟨t, hh, q⟩ := c
  simp only at h
  subst h
  exact stepU_fail t hh

theorem iterate_halt (c : PCfg U n0) (h : c.state = .halt) (m : ℕ) : (stepU)^[m] c = c := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, stepU_state_halt c h]

theorem iterate_fail (c : PCfg U n0) (h : c.state = .fail) (m : ℕ) : (stepU)^[m] c = c := by
  induction m with
  | zero => rfl
  | succ m ih => rw [Function.iterate_succ_apply', ih, stepU_state_fail c h]

/-- Before a time at which the run is not in HALT, it is never in HALT. -/
theorem not_halt_before (c : PCfg U n0) {T : ℕ} (hT : ((stepU)^[T] c).state ≠ .halt) {i : ℕ}
    (hi : i ≤ T) : ((stepU)^[i] c).state ≠ .halt := by
  intro h
  apply hT
  rw [show T = (T - i) + i by omega, Function.iterate_add_apply, iterate_halt _ h]
  exact h

/-- After a time at which the run is in FAIL, it stays in FAIL. -/
theorem fail_after (c : PCfg U n0) {T : ℕ} (hT : ((stepU)^[T] c).state = .fail) {i : ℕ}
    (hi : T ≤ i) : ((stepU)^[i] c).state = .fail := by
  rw [show i = (i - T) + T by omega, Function.iterate_add_apply, iterate_fail _ hT]
  exact hT

/-- A run that reaches FAIL never enters HALT. -/
theorem never_halt_of_fail (c : PCfg U n0) {T : ℕ} (hT : ((stepU)^[T] c).state = .fail) (i : ℕ) :
    ((stepU)^[i] c).state ≠ .halt := by
  rcases le_total i T with h | h
  · exact not_halt_before c (by rw [hT]; simp) h
  · rw [fail_after c hT h]; simp

/-! ## Forgetting the read-only input tracks -/

/-- Erase the read-only input tracks `h_in`, `π`. -/
def forgetT (g : Tape U) : Tape U := { g with hin := false, pi := false }

/-- Erase the read-only input tracks on the whole tape. -/
def forgetC (c : PCfg U n0) : PCfg U n0 := ⟨fun j => forgetT (c.tape j), c.head, c.state⟩

/-- Away from SCAN, the program neither reads nor writes `h_in`, `π`. -/
theorem program_forget (q : PState U n0) (hq : q ≠ .scan) (g : Tape U) :
    program U n0 q (forgetT g) =
      (program U n0 q g).map (fun r => (r.1, forgetT r.2.1, r.2.2)) := by
  obtain ⟨hin, pi, z, p, e, n, u⟩ := g
  change program U n0 q ⟨false, false, z, p, e, n, u⟩ = _
  cases q <;> first
    | exact absurd rfl hq
    | rfl
    | (simp only [program]; split_ifs <;> rfl)

theorem deltaP_forget (q : PState U n0) (hq : q ≠ .scan) (g : Tape U) :
    deltaP U n0 q (forgetT g) =
      ((deltaP U n0 q g).1, forgetT (deltaP U n0 q g).2.1, (deltaP U n0 q g).2.2) := by
  unfold deltaP
  rw [program_forget q hq g]
  cases program U n0 q g <;> rfl

/-- SCAN is never re-entered. -/
theorem deltaP_ne_scan (q : PState U n0) (hq : q ≠ .scan) (g : Tape U) :
    (deltaP U n0 q g).1 ≠ .scan := by
  unfold deltaP
  cases q with
  | scan => exact absurd rfl hq
  | ret c => cases c <;> by_cases hz : g.z <;> simp [program, hz, Cont.state]
  | r b c =>
    simp only [program]
    split_ifs <;> simp
  | appendN => simp only [program]; split_ifs <;> simp
  | skip c => simp only [program]; split_ifs <;> simp
  | findN => simp only [program]; split_ifs <;> simp
  | appendU => simp only [program]; split_ifs <;> simp
  | run q => simp only [program]; split_ifs <;> simp
  | _ => simp [program]

theorem stepU_ne_scan (c : PCfg U n0) (hc : c.state ≠ .scan) : (stepU c).state ≠ .scan := by
  obtain ⟨t, h, q⟩ := c
  have := deltaP_ne_scan q hc (t h)
  unfold stepU
  split <;> simp only [ne_eq] <;> try exact this
  split <;> simp_all

theorem update_forget (t : ℕ → Tape U) (h : ℕ) (g : Tape U) :
    Function.update (fun j => forgetT (t j)) h (forgetT g) =
      fun j => forgetT (Function.update t h g j) := by
  funext j
  by_cases hj : j = h
  · subst hj; simp
  · simp [Function.update_of_ne hj]

theorem stepU_forget (c : PCfg U n0) (hc : c.state ≠ .scan) :
    stepU (forgetC c) = forgetC (stepU c) := by
  obtain ⟨t, h, q⟩ := c
  have hd := deltaP_forget q hc (t h)
  simp only [forgetC, stepU, hd]
  split <;> (try split) <;> simp_all [update_forget]

/-- **The run commutes with forgetting the input tracks** (away from SCAN). -/
theorem iterate_forget (c : PCfg U n0) (hc : c.state ≠ .scan) (k : ℕ) :
    (stepU)^[k] (forgetC c) = forgetC ((stepU)^[k] c) := by
  induction k generalizing c with
  | zero => rfl
  | succ k ih =>
    rw [Function.iterate_succ_apply, Function.iterate_succ_apply, stepU_forget c hc]
    exact ih _ (stepU_ne_scan c hc)

/-- The state along the run does not depend on the input tracks (away from SCAN). -/
theorem state_iterate_forget (c : PCfg U n0) (hc : c.state ≠ .scan) (k : ℕ) :
    ((stepU)^[k] (forgetC c)).state = ((stepU)^[k] c).state := by
  rw [iterate_forget c hc]; rfl

/-! ## The SCAN phase -/

theorem deltaP_scan_one (g : Tape U) (hg : g.hin = true) :
    deltaP U n0 .scan g = (.scan, { g with p := true }, .up) := by
  simp [deltaP, program, hg]

theorem deltaP_scan_plus (g : Tape U) (hg : g.hin = false) (hpi : g.pi = true) :
    deltaP U n0 .scan g = (.plus, { g with p := true }, .up) := by
  simp [deltaP, program, hg, hpi]

theorem deltaP_scan_fail (g : Tape U) (hg : g.hin = false) (hpi : g.pi = false) :
    deltaP U n0 .scan g = (.fail, g, .stay) := by
  simp [deltaP, program, hg, hpi]

/-- SCAN over the ones of `h_in` below `js`: marks `p_* = 1` there. -/
theorem scan_phase (h pi : ℕ → Bool) (js : ℕ) (hh : ∀ j < js, h j = true) :
    (stepU)^[js] (cfg0 U n0 h pi) =
      ⟨fun j => if 0 ≤ j ∧ j < 0 + js then { tape0 U h pi j with p := true } else tape0 U h pi j,
        0 + js, .scan⟩ :=
  scan_up .scan (fun g => { g with p := true }) (fun g => g.hin = true)
    (fun g hg => deltaP_scan_one g hg) (tape0 U h pi) 0 js
    (fun j _ hj => by simp [tape0, hh j (by omega)])

/-- The tape after SCAN and its first step past the initial zero: `p_* = 1` on `0, …, j_*`. -/
def tape1 (U : Machine) (h pi : ℕ → Bool) (js : ℕ) : ℕ → Tape U :=
  fun j => if j ≤ js then { tape0 U h pi j with p := true } else tape0 U h pi j

/-- **SCAN, parity bit one**: after `j_* + 1` steps the head is at `j_* + 1` in PLUS. -/
theorem scan_plus (h pi : ℕ → Bool) (js : ℕ) (hh : ∀ j < js, h j = true) (h0 : h js = false)
    (hpi : pi js = true) :
    (stepU)^[js + 1] (cfg0 U n0 h pi) = ⟨tape1 U h pi js, js + 1, .plus⟩ := by
  rw [Function.iterate_succ_apply', scan_phase h pi js hh, zero_add]
  have hd : deltaP U n0 .scan
      ((fun j => if 0 ≤ j ∧ j < js then { tape0 U h pi j with p := true } else tape0 U h pi j) js) =
      (.plus, { tape0 U h pi js with p := true }, .up) := by
    dsimp only
    rw [ite_eq_right (by omega)]
    exact deltaP_scan_plus _ (by simp [tape0, h0]) (by simp [tape0, hpi])
  rw [stepU_up hd]
  congr 1
  funext j
  by_cases hj : j = js
  · subst hj; simp [tape1]
  · rw [Function.update_of_ne hj]
    by_cases hlt : j < js
    · simp [tape1, hlt, show j ≤ js by omega]
    · simp [tape1, hlt, show ¬ j ≤ js by omega]

/-- **The parity guard**: if the initial zero of `h_in` (at `j₀`) has parity bit zero, the run
is in FAIL after `j₀ + 1` steps, and it never enters HALT. -/
theorem scan_guard (h pi : ℕ → Bool) (j0 : ℕ) (hh : ∀ j < j0, h j = true) (h0 : h j0 = false)
    (hpi : pi j0 = false) (i : ℕ) : ((stepU)^[i] (cfg0 U n0 h pi)).state ≠ .halt := by
  have hT : ((stepU)^[j0 + 1] (cfg0 U n0 h pi)).state = .fail := by
    rw [Function.iterate_succ_apply', scan_phase h pi j0 hh, zero_add]
    have hd : deltaP U n0 .scan
        ((fun j => if 0 ≤ j ∧ j < j0 then { tape0 U h pi j with p := true } else
          tape0 U h pi j) j0) = (.fail, tape0 U h pi j0, .stay) := by
      dsimp only
      rw [ite_eq_right (by omega)]
      exact deltaP_scan_fail _ (by simp [tape0, h0]) (by simp [tape0, hpi])
    rw [stepU_stay hd]
  exact never_halt_of_fail _ hT i

/-- **No zero**: if `h_in` has no zero, the run stays in SCAN, never in HALT. -/
theorem scan_forever (h pi : ℕ → Bool) (hh : ∀ j, h j = true) (i : ℕ) :
    ((stepU)^[i] (cfg0 U n0 h pi)).state ≠ .halt := by
  rw [scan_phase h pi i (fun j _ => hh j)]
  simp

/-! ## RUN simulates `U` -/

/-- The work tape after SCAN (input tracks erased): `z = [j = 0]`, marks `P`, the end mark at
`M`, tokens `N`, and the `u_*` track `V`. -/
def wt (U : Machine) (M : ℕ) (P : ℕ → Bool) (N : ℕ → Fin 3) (V : ℕ → U.Symbol) : ℕ → Tape U :=
  fun j => ⟨false, false, decide (j = 0), P j, decide (j = M), N j, V j⟩

theorem wt_z (M : ℕ) (P : ℕ → Bool) (N : ℕ → Fin 3) (V : ℕ → U.Symbol) (j : ℕ) :
    (wt U M P N V j).z = decide (j = 0) := rfl

theorem update_wt_u (M : ℕ) (P : ℕ → Bool) (N : ℕ → Fin 3) (V : ℕ → U.Symbol) (h : ℕ)
    (x : U.Symbol) :
    Function.update (wt U M P N V) h { wt U M P N V h with u := x } =
      wt U M P N (Function.update V h x) := by
  funext j
  by_cases hj : j = h
  · subst hj; simp [wt]
  · simp [wt, Function.update_of_ne hj]

/-- The configuration of `P` simulating the configuration `c` of `U`. -/
def sim (M : ℕ) (P : ℕ → Bool) (N : ℕ → Fin 3) (c : U.Cfg) : PCfg U n0 :=
  ⟨wt U M P N c.tape, c.head, .run c.state⟩

theorem deltaP_run (q : U.State) (hq : U.halting q = false) (g : Tape U) :
    deltaP U n0 (.run q) g =
      ((if U.halting (U.trans q g.u).1 then .halt else .run (U.trans q g.u).1),
        { g with u := (U.trans q g.u).2.1 }, if (U.trans q g.u).2.2 then .up else .down) := by
  simp [deltaP, program, hq]

/-- **One step of RUN is one step of `U`** (a halting successor enters HALT). -/
theorem sim_step (M : ℕ) (P : ℕ → Bool) (N : ℕ → Fin 3) (c c' : U.Cfg)
    (hq : U.halting c.state = false) (hs : U.step c = some c') :
    stepU (sim (n0 := n0) M P N c) =
      ⟨wt U M P N c'.tape, c'.head,
        if U.halting c'.state then .halt else .run c'.state⟩ := by
  obtain ⟨q, hd, tp⟩ := c
  have hdel := deltaP_run (n0 := n0) q hq (wt U M P N tp hd)
  simp only [wt] at hdel
  simp only [Machine.step] at hs
  by_cases hdir : (U.trans q (tp hd)).2.2 = true
  · rw [ite_eq_left hdir] at hs
    obtain rfl := Option.some.inj hs
    simp only [sim, hdir, ite_true] at hdel ⊢
    rw [stepU_up hdel]
    congr 1
    exact update_wt_u M P N tp hd _
  · rw [ite_eq_right hdir] at hs
    by_cases hz : hd = 0
    · rw [ite_eq_left hz] at hs
      exact absurd hs (by simp)
    · rw [ite_eq_right hz] at hs
      obtain rfl := Option.some.inj hs
      simp only [sim, hdir, ite_false, Bool.false_eq_true] at hdel ⊢
      rw [stepU_down hdel hz]
      congr 1
      exact update_wt_u M P N tp hd _

/-- **An attempted move left from cell `0` fails.** -/
theorem sim_step_none (M : ℕ) (P : ℕ → Bool) (N : ℕ → Fin 3) (c : U.Cfg)
    (hq : U.halting c.state = false) (hs : U.step c = none) :
    (stepU (sim (n0 := n0) M P N c)).state = .fail := by
  obtain ⟨q, hd, tp⟩ := c
  have hdel := deltaP_run (n0 := n0) q hq (wt U M P N tp hd)
  simp only [wt] at hdel
  simp only [Machine.step] at hs
  by_cases hdir : (U.trans q (tp hd)).2.2 = true
  · rw [ite_eq_left hdir] at hs
    exact absurd hs (by simp)
  · rw [ite_eq_right hdir] at hs
    by_cases hz : hd = 0
    · subst hz
      simp only [sim, hdir, ite_false, Bool.false_eq_true] at hdel ⊢
      rw [stepU_down_zero hdel]
    · rw [ite_eq_right hz] at hs
      exact absurd hs (by simp)

theorem run_succ (L t : ℕ) : U.run L (t + 1) = (U.run L t).bind U.step := rfl

/-- **The simulation invariant**: while `U` has not halted, the run from `sim (start L)` is the
simulation of `U`'s run on `L`, or it is in FAIL after `U`'s run ended by a move off cell `0`. -/
theorem sim_inv (M : ℕ) (P : ℕ → Bool) (N : ℕ → Fin 3) (L k : ℕ)
    (hk : ∀ t ≤ k, ∀ c, U.run L t = some c → U.halting c.state = false) :
    (∃ c, U.run L k = some c ∧ (stepU)^[k] (sim (n0 := n0) M P N (U.start L)) = sim M P N c) ∨
      (U.run L k = none ∧ ((stepU)^[k] (sim (n0 := n0) M P N (U.start L))).state = .fail) := by
  induction k with
  | zero => exact Or.inl ⟨U.start L, rfl, rfl⟩
  | succ k ih =>
    rcases ih (fun t ht c hc => hk t (by omega) c hc) with ⟨c, hc, he⟩ | ⟨hn, hf⟩
    · have hq := hk k (by omega) c hc
      rw [Function.iterate_succ_apply', he, run_succ, hc]
      rcases hs : U.step c with _ | c'
      · right
        exact ⟨by simp [hs], sim_step_none M P N c hq hs⟩
      · left
        have hq' := hk (k + 1) le_rfl c' (by rw [run_succ, hc]; simp [hs])
        refine ⟨c', by simp [hs], ?_⟩
        rw [sim_step M P N c c' hq hs, hq']
        rfl
    · right
      rw [run_succ, hn, Function.iterate_succ_apply', stepU_state_fail _ hf]
      exact ⟨rfl, hf⟩

/-- **If `U` halts on `L`, the simulation reaches HALT.** -/
theorem sim_halts (M : ℕ) (P : ℕ → Bool) (N : ℕ → Fin 3) (L : ℕ) (hU : U.HaltsOn L) :
    ∃ k, ((stepU)^[k] (sim (n0 := n0) M P N (U.start L))).state = .halt := by
  classical
  have hex : ∃ t, ∃ c, U.run L t = some c ∧ U.halting c.state = true := by
    obtain ⟨t, c, h1, h2⟩ := hU
    exact ⟨t, c, h1, h2⟩
  set t0 := Nat.find hex with ht0
  obtain ⟨c0, hc0, hhalt⟩ := Nat.find_spec hex
  have hmin : ∀ t < t0, ∀ c, U.run L t = some c → U.halting c.state = false := by
    intro t ht c hc
    have := Nat.find_min hex ht
    push Not at this
    cases hh : U.halting c.state
    · rfl
    · exact absurd hh (by simpa using this c hc)
  have hpos : t0 ≠ 0 := by
    intro h0
    rw [← ht0, h0] at hc0
    have : U.start L = c0 := Option.some.inj hc0
    rw [← this] at hhalt
    simp [Machine.start, U.init_not_halting] at hhalt
  obtain ⟨s, hs⟩ : ∃ s, t0 = s + 1 := ⟨t0 - 1, by omega⟩
  rcases sim_inv (n0 := n0) M P N L s (fun t ht c hc => hmin t (by omega) c hc) with
    ⟨c, hc, he⟩ | ⟨hn, -⟩
  · have hq := hmin s (by omega) c hc
    have hs' : U.step c = some c0 := by
      have := hc0
      rw [← ht0, hs, run_succ, hc] at this
      simpa using this
    refine ⟨s + 1, ?_⟩
    rw [Function.iterate_succ_apply', he, sim_step M P N c c0 hq hs', hhalt]
    rfl
  · exfalso
    have := hc0
    rw [← ht0, hs, run_succ, hn] at this
    simp at this

/-- **If `U` does not halt on `L`, the simulation never enters HALT.** -/
theorem sim_no_halt (M : ℕ) (P : ℕ → Bool) (N : ℕ → Fin 3) (L : ℕ) (hU : ¬ U.HaltsOn L) (k : ℕ) :
    ((stepU)^[k] (sim (n0 := n0) M P N (U.start L))).state ≠ .halt := by
  have hk : ∀ t ≤ k, ∀ c, U.run L t = some c → U.halting c.state = false := by
    intro t _ c hc
    cases hh : U.halting c.state
    · rfl
    · exact absurd ⟨t, c, hc, hh⟩ hU
  rcases sim_inv (n0 := n0) M P N L k hk with ⟨c, -, he⟩ | ⟨-, hf⟩
  · rw [he]; simp [sim]
  · rw [hf]; simp

end UND.MachineP
