/-
# Lemma 3.3, indexed: a board carries the run of `P` (D27)

The indexed packaging of Lemma 3.3 (`BLUEPRINT.md`, S8, D27) for the content alphabet of the
machine `P`, NEW. Paper (Lemma 3.3): "… the board `{(x_i, y_j) : 0 ≤ i, j < N_d}`. Here
`x_0 < ⋯ < x_{N_d-1}` and `y_0 < ⋯ < y_{N_d-1}` list the free coordinates. … Its central contents
`s_i(j) = t_C(x_i, y_j)` obey `s_0(j) = init(H_row(y_j), χ₂(y_j), [j = 0])`,
`s_{i+1}(j) = f_P(s_i(j-1), s_i(j), s_i(j+1))`, `s_i(-1) = s_i(N_d) = ⊥`. Thus it contains the
unique `N_d`-cell, `(N_d - 1)`-step finite-tape computation."

* `FreeOff t d m n` (`r_d(m) + n` is free), `freeOff_finite`, **`count_freeOff`**
  (`N_d = 2^{d+2} - 2` free coordinates, from the hard-model core's `card_free`), `card_freeOff`;
* `freeAt t d m i` (the `i`-th free coordinate, by `Nat.nth`), `freeAt_free`, `freeAt_zero`
  (`L_* + 1`), `freeAt_last` (`R_* - 1`), `freeAt_lt`, `freeAt_consec` (no free coordinate
  between consecutive ones), `freeAt_eq_zero_iff`;
* `boardH`, `boardPi` (the input tracks read at the board's free rows);
* **`board_run`**: in every phase, the record at `(x_i, y_j)` has central content
  `runP U n₀ N_d (boardH) (boardPi) i j`, the board run of `P` (Lemma 4.1(a) identifies it with the
  sequential machine).
-/
import UncomputableNoiseDiagram.Chart.BoardTableau
import UncomputableNoiseDiagram.Chart.Input
import UncomputableNoiseDiagram.Chart.TheCA
import UncomputableNoiseDiagram.Machine.Decode

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UND.Chart

open UPD UPD.Scaffold

/-! ## The free coordinates of a frame, indexed -/

/-- `r_d(m) + n` is a free coordinate of `I_d(m)`. -/
def FreeOff (t : ℕ → Bool) (d : ℕ) (m : ℤ) (n : ℕ) : Prop :=
  IsFree (phaseOffsets t) d m (rfree (phaseOffsets t) d m + n)

/-- `N_d = 2^{d+2} - 2`. -/
abbrev Nd (d : ℕ) : ℕ := 2 ^ (d + 2) - 2

theorem freeOff_finite (t : ℕ → Bool) (d : ℕ) (m : ℤ) : (Set.ofPred (FreeOff t d m)).Finite :=
  (Set.finite_lt_nat (2 * 4 ^ d)).subset fun n hn => by
    have := lt_of_isFree (t := t) (show FreeOff t d m n from hn)
    show n < 2 * 4 ^ d
    omega

open Classical in
/-- `N_d` free coordinates (the hard-model core's `card_free`), counted by offsets. -/
theorem count_freeOff (t : ℕ → Bool) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) :
    Nat.count (FreeOff t d m) (2 * 4 ^ d - 2) = Nd d := by
  rw [Nd, ← card_free (frameOffsets_phase t) hd m, Nat.count_eq_card_filter_range]
  have hset : {z | IsFree (phaseOffsets t) d m z} =
      ↑(((Finset.range (2 * 4 ^ d - 2)).filter (FreeOff t d m)).image
        (fun n : ℕ => rfree (phaseOffsets t) d m + n)) := by
    ext z
    simp only [Set.mem_ofPred_eq, Finset.coe_image, Finset.coe_filter, Set.mem_image,
      Finset.mem_range, FreeOff]
    constructor
    · intro hz
      have h1 := hz.1
      have hge : 0 ≤ z - rfree (phaseOffsets t) d m := by simp only [rfree]; omega
      have hz' : rfree (phaseOffsets t) d m + ((z - rfree (phaseOffsets t) d m).toNat : ℤ) = z := by
        rw [Int.toNat_of_nonneg hge]; ring
      have hfree : IsFree (phaseOffsets t) d m
          (rfree (phaseOffsets t) d m + ((z - rfree (phaseOffsets t) d m).toNat : ℕ)) := by
        rw [hz']; exact hz
      exact ⟨_, ⟨by have := lt_of_isFree hfree; omega, hfree⟩, hz'⟩
    · rintro ⟨n, ⟨-, hn⟩, rfl⟩
      exact hn
  rw [hset, Set.ncard_coe_finset,
    Finset.card_image_of_injective _ (fun x y h => by simpa using h)]

open Classical in
theorem card_freeOff (t : ℕ → Bool) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) :
    (freeOff_finite t d m).toFinset.card = Nd d := by
  rw [← count_freeOff t hd m, Nat.count_eq_card_filter_range]
  congr 1
  ext n
  simp only [Set.Finite.mem_toFinset, Finset.mem_filter, Finset.mem_range]
  constructor
  · intro hn
    have := lt_of_isFree (t := t) (show FreeOff t d m n from hn)
    exact ⟨by omega, hn⟩
  · exact fun h => h.2

/-- The `i`-th free coordinate of `I_d(m)` (`x_i` or `y_i`). -/
def freeAt (t : ℕ → Bool) (d : ℕ) (m : ℤ) (i : ℕ) : ℤ :=
  rfree (phaseOffsets t) d m + (Nat.nth (FreeOff t d m) i : ℕ)

theorem freeOff_nth (t : ℕ → Bool) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {i : ℕ} (hi : i < Nd d) :
    FreeOff t d m (Nat.nth (FreeOff t d m) i) :=
  Nat.nth_mem_of_lt_card (freeOff_finite t d m) (by rw [card_freeOff t hd m]; exact hi)

theorem freeAt_free (t : ℕ → Bool) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {i : ℕ} (hi : i < Nd d) :
    IsFree (phaseOffsets t) d m (freeAt t d m i) :=
  freeOff_nth t hd m hi

theorem freeOff_zero (t : ℕ → Bool) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) : FreeOff t d m 0 := by
  unfold FreeOff
  rw [Nat.cast_zero, add_zero]
  exact isFree_rfree (frameOffsets_phase t) hd m

theorem nth_freeOff_zero (t : ℕ → Bool) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) :
    Nat.nth (FreeOff t d m) 0 = 0 :=
  Nat.nth_zero_of_zero (freeOff_zero t hd m)

/-- `x_0 = L_* + 1`. -/
theorem freeAt_zero (t : ℕ → Bool) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) :
    freeAt t d m 0 = frameLo (phaseOffsets t) d m + 1 := by
  rw [freeAt, nth_freeOff_zero t hd m]
  simp [rfree]

theorem freeAt_lt (t : ℕ → Bool) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {i j : ℕ} (hij : i < j)
    (hj : j < Nd d) : freeAt t d m i < freeAt t d m j := by
  have := Nat.nth_lt_nth_of_lt_card (freeOff_finite t d m) hij
    (by rw [card_freeOff t hd m]; exact hj)
  simp only [freeAt]
  omega

theorem freeAt_eq_zero_iff (t : ℕ → Bool) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) {j : ℕ} (hj : j < Nd d) :
    freeAt t d m j = frameLo (phaseOffsets t) d m + 1 ↔ j = 0 := by
  constructor
  · intro h
    by_contra h0
    have := freeAt_lt t hd m (Nat.pos_of_ne_zero h0) hj
    rw [freeAt_zero t hd m, h] at this
    exact lt_irrefl _ this
  · rintro rfl
    exact freeAt_zero t hd m

/-- Consecutive free coordinates: nothing free strictly between `x_i` and `x_{i+1}`. -/
theorem freeAt_consec (t : ℕ → Bool) {d : ℕ} (m : ℤ) {i : ℕ} (z : ℤ) (h1 : freeAt t d m i < z) (h2 : z < freeAt t d m (i + 1)) :
    ¬ IsFree (phaseOffsets t) d m z := by
  intro hz
  have hge : 0 ≤ z - rfree (phaseOffsets t) d m := by
    simp only [freeAt] at h1; omega
  have hz' : rfree (phaseOffsets t) d m + ((z - rfree (phaseOffsets t) d m).toNat : ℤ) = z := by
    rw [Int.toNat_of_nonneg hge]; ring
  have hf : FreeOff t d m (z - rfree (phaseOffsets t) d m).toNat := by
    unfold FreeOff; rw [hz']; exact hz
  have hlt : (z - rfree (phaseOffsets t) d m).toNat < Nat.nth (FreeOff t d m) (i + 1) := by
    simp only [freeAt] at h2; omega
  have := Nat.le_nth_of_lt_nth_succ hlt hf
  simp only [freeAt] at h1
  omega

open Classical in
/-- `x_{N_d - 1} = R_* - 1`. -/
theorem freeAt_last (t : ℕ → Bool) {d : ℕ} (hd : 1 ≤ d) (m : ℤ) :
    freeAt t d m (Nd d - 1) = frameHi (phaseOffsets t) d m - 1 := by
  have h4 : 4 ≤ 4 ^ d := le_self_pow₀ (by norm_num) (by omega)
  have hlast : FreeOff t d m (2 * 4 ^ d - 3) := by
    unfold FreeOff
    have e : rfree (phaseOffsets t) d m + ((2 * 4 ^ d - 3 : ℕ) : ℤ) =
        frameHi (phaseOffsets t) d m - 1 := by
      have : ((2 * 4 ^ d - 3 : ℕ) : ℤ) = 2 * 4 ^ d - 3 := by push_cast [show 3 ≤ 2 * 4 ^ d by omega]; ring
      rw [this]; simp only [rfree, frameLo, frameHi]; ring
    rw [e]
    exact isFree_frameHi_sub_one (frameOffsets_phase t) hd m
  have hc : Nat.count (FreeOff t d m) (2 * 4 ^ d - 3) = Nd d - 1 := by
    have h := count_freeOff t hd m
    rw [show 2 * 4 ^ d - 2 = (2 * 4 ^ d - 3) + 1 by omega, Nat.count_succ, ite_eq_left hlast] at h
    omega
  rw [freeAt, ← hc, Nat.nth_count hlast]
  have : ((2 * 4 ^ d - 3 : ℕ) : ℤ) = 2 * 4 ^ d - 3 := by push_cast [show 3 ≤ 2 * 4 ^ d by omega]; ring
  rw [this]; simp only [rfree, frameLo, frameHi]; ring

/-! ## The board carries the run of `P` -/

variable {U : Machine} {n0 k : ℕ} {c : Plane → RTile (contentP U n0) k} {τ : ℕ → Bool × Bool}

/-- The input track `h_in` of a board: `H_row` at the free rows (read on the first free column). -/
def boardH (c : Plane → RTile (contentP U n0) k) (τ : ℕ → Bool × Bool) (d : ℕ) (m₁ m₂ : ℤ)
    (j : ℕ) : Bool :=
  (c (freeAt (col τ) d m₁ 0, freeAt (row τ) d m₂ j)).1.1.q.H

/-- The input track `π` of a board: `χ₂` at the free rows. -/
def boardPi (c : Plane → RTile (contentP U n0) k) (τ : ℕ → Bool × Bool) (d : ℕ) (m₁ m₂ : ℤ)
    (j : ℕ) : Bool :=
  (c (freeAt (col τ) d m₁ 0, freeAt (row τ) d m₂ j)).1.1.q.parent.1.a.1.b2

/-- **Lemma 3.3, indexed** (every phase): the record at the board site `(x_i, y_j)` has central
content `s_i(j) = runP U n₀ N_d (H_row) (χ₂) i j`: the board carries the run of `P` on its `N_d`
free rows, initialized by `init(H_row(y_j), χ₂(y_j), [j = 0])`. -/
theorem board_run (hc : IsRChart (contentP U n0) k c)
    (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ) {d : ℕ} (hd : 1 ≤ d) (m₁ m₂ : ℤ) :
    ∀ i, i < Nd d → ∀ j : Fin (Nd d), ∃ tS tN,
      (c (freeAt (col τ) d m₁ i, freeAt (row τ) d m₂ j)).1.1.k =
        some (tS, MachineP.runP U n0 (Nd d) (boardH c τ d m₁ m₂) (boardPi c τ d m₁ m₂) i j, tN) := by
  have hN : 2 ≤ Nd d := by
    have : 8 ≤ 2 ^ (d + 2) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (d + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    show 2 ≤ 2 ^ (d + 2) - 2
    omega
  have hx : ∀ i, i < Nd d → IsFree (phaseOffsets (col τ)) d m₁ (freeAt (col τ) d m₁ i) :=
    fun i hi => freeAt_free (col τ) hd m₁ hi
  have hy : ∀ j, j < Nd d → IsFree (phaseOffsets (row τ)) d m₂ (freeAt (row τ) d m₂ j) :=
    fun j hj => freeAt_free (row τ) hd m₂ hj
  intro i
  induction i with
  | zero =>
    intro _ j
    obtain ⟨tS, tC, tN, hk, -, -⟩ := board_record hc hτ hd m₁ m₂ (hx 0 (by omega)) (hy j j.2)
    refine ⟨tS, tN, ?_⟩
    rw [hk]
    have hk' := hk
    rw [freeAt_zero (col τ) hd m₁] at hk'
    have hinit := board_init hc hτ hd m₁ m₂ (hy j j.2) hk'
    rw [hinit, ← freeAt_zero (col τ) hd m₁]
    have hz : decide (freeAt (row τ) d m₂ j = frameLo (phaseOffsets (row τ)) d m₂ + 1) =
        decide (j.val = 0) := by
      simp only [decide_eq_decide]
      exact freeAt_eq_zero_iff (row τ) hd m₂ j.2
    rw [hz]
    rfl
  | succ i ih =>
    intro hi j
    obtain ⟨tS, tC, tN, hk, -, -⟩ := board_record hc hτ hd m₁ m₂ (hx (i + 1) hi) (hy j j.2)
    refine ⟨tS, tN, ?_⟩
    rw [hk]
    obtain ⟨tS₀, tN₀, hk₀⟩ := ih (by omega) j
    have hstep := board_step hc hτ hd m₁ m₂ (hx i (by omega)) (hx (i + 1) hi)
      (freeAt_lt (col τ) hd m₁ (Nat.lt_succ_self i) hi)
      (fun z h1 h2 => freeAt_consec (col τ) m₁ z h1 h2) (hy j j.2) hk₀ hk
    -- the south entry
    have hS : tS₀ = (if h : 0 < j.val then some (MachineP.runP U n0 (Nd d) (boardH c τ d m₁ m₂)
        (boardPi c τ d m₁ m₂) i ⟨j.val - 1, by omega⟩) else none) := by
      by_cases h0 : 0 < j.val
      · rw [dite_eq_left h0]
        obtain ⟨tS₁, tN₁, hk₁⟩ := ih (by omega) ⟨j.val - 1, by omega⟩
        have hv := board_vlink hc hτ hd m₁ m₂ (hx i (by omega)) (hy (j.val - 1) (by omega))
          (hy j j.2) (freeAt_lt (row τ) hd m₂ (by omega) j.2)
          (fun z h1 h2 => by
            have := freeAt_consec (row τ) m₂ (i := j.val - 1) z h1
            rw [show j.val - 1 + 1 = j.val by omega] at this
            exact this h2) hk₁ hk₀
        exact hv.2
      · rw [dite_eq_right h0]
        have hj0 : j.val = 0 := by omega
        have hk₀' := hk₀
        rw [show (j : ℕ) = 0 from hj0, freeAt_zero (row τ) hd m₂] at hk₀'
        exact board_bottom hc hτ hd m₁ m₂ (hx i (by omega)) hk₀'
    -- the north entry
    have hNo : tN₀ = (if h : j.val + 1 < Nd d then some (MachineP.runP U n0 (Nd d)
        (boardH c τ d m₁ m₂) (boardPi c τ d m₁ m₂) i ⟨j.val + 1, h⟩) else none) := by
      by_cases h1 : j.val + 1 < Nd d
      · rw [dite_eq_left h1]
        obtain ⟨tS₁, tN₁, hk₁⟩ := ih (by omega) ⟨j.val + 1, h1⟩
        have hv := board_vlink hc hτ hd m₁ m₂ (hx i (by omega)) (hy j j.2) (hy (j.val + 1) h1)
          (freeAt_lt (row τ) hd m₂ (Nat.lt_succ_self _) h1)
          (fun z h1' h2' => freeAt_consec (row τ) m₂ z h1' h2') hk₀ hk₁
        exact hv.1
      · rw [dite_eq_right h1]
        have hjl : j.val = Nd d - 1 := by have := j.2; omega
        have hk₀' := hk₀
        rw [show (j : ℕ) = Nd d - 1 from hjl, freeAt_last (row τ) hd m₂] at hk₀'
        exact board_top hc hτ hd m₁ m₂ (hx i (by omega)) hk₀'
    rw [hstep, hS, hNo]
    simp only [MachineP.runP, Function.iterate_succ_apply']
    rfl

end UND.Chart
