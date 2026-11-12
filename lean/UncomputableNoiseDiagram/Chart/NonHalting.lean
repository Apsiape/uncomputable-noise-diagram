/-
# Prop 4.3, the nonhalting branch: boards under the correct cutoff never halt (M5, first part)

Part of node M5 of `BLUEPRINT.md` (Part A.4), NEW. Paper (Prop 4.3, proof, nonhalting): "Fill
every board with its initialized finite run. Large boards decode `n` by Lemmas 4.2 and 4.1; small
boards fail or reach a boundary. A finite exit fails, so none contains HALT."

The input tracks of a board under the cutoff `b_r = [r < cut]` (the chart the construction will
build) are `h_in(j) = [rank(y_j) < cut]`, `π(j) = rank(y_j) mod 2` (Lemma 3.2, `chi2_eq`).
* `prankOf` (the parent rank as a function), `prankOf_spec`, `prankOf_eq`;
* `cutH`, `cutPi` (the input tracks of the depth-`d` board of `I_d(m)`);
* **`board_no_halt`**: if `U` does not halt on `n ≥ 1` (`n₀ ≥ 1`, `a = n + n₀`) and
  `cut ∈ {2a - 2, 2a - 1}`, the run of `P` on these tracks never enters HALT, for every depth
  `d ≥ 1` and every frame, in every phase (large boards decode `n`: `decode_no_halt`; small boards
  are rejected by the parity guard: `guard_no_halt`);
* **`board_run_no_halt`**: hence no content of the board run carries HALT (`runP_no_halt`).
-/
import UncomputableNoiseDiagram.Chart.Halting

set_option autoImplicit false

noncomputable section

namespace UND.Chart

open UPD UPD.Scaffold

open Classical in
/-- The parent rank of `z` as a function (`0` when it has none). -/
def prankOf (t : ℕ → Bool) (z : ℤ) : ℕ := if h : ∃ r, PRank t z r then Nat.find h else 0

theorem prankOf_spec {t : ℕ → Bool} {z : ℤ} (h : ∃ r, PRank t z r) :
    PRank t z (prankOf t z) := by
  classical
  unfold prankOf
  rw [dite_eq_left h]
  exact Nat.find_spec h

theorem prankOf_eq {t : ℕ → Bool} {z : ℤ} {r : ℕ} (h : PRank t z r) : prankOf t z = r :=
  (prankOf_spec ⟨r, h⟩).unique h

/-- The input track `h_in` of the depth-`d` board of `I_d(m)` under the cutoff `cut`:
`[rank(y_j) < cut]` on its `N_d` rows (`1` beyond). -/
def cutH (t : ℕ → Bool) (d : ℕ) (m : ℤ) (cut : ℕ) (j : ℕ) : Bool :=
  if j < Nd d then decide (prankOf t (freeAt t d m j) < cut) else true

/-- The input track `π` of the depth-`d` board: the parity of `rank(y_j)`. -/
def cutPi (t : ℕ → Bool) (d : ℕ) (m : ℤ) (j : ℕ) : Bool :=
  decide (prankOf t (freeAt t d m j) % 2 = 1)

/-- **Prop 4.3, nonhalting: no board halts.** If `U` does not halt on `n ≥ 1` (`n₀ ≥ 1`,
`a = n + n₀`) and `cut ∈ {2a - 2, 2a - 1}`, the run of `P` on the input tracks of any depth-`d`
board under the cutoff `cut` never enters HALT (every phase). -/
theorem board_no_halt {U : UPD.Machine} {n0 n : ℕ} (hn : 1 ≤ n) (hn0 : 1 ≤ n0)
    (hU : ¬ U.HaltsOn n) (t : ℕ → Bool) {cut : ℕ}
    (hcut : cut = 2 * (n + n0) - 2 ∨ cut = 2 * (n + n0) - 1) {d : ℕ} (hd : 1 ≤ d) (m : ℤ)
    (i : ℕ) :
    ((MachineP.stepU)^[i] (MachineP.cfg0 U n0 (cutH t d m cut) (cutPi t d m))).state ≠ .halt := by
  classical
  set a := n + n0 with ha
  have ha2 : 2 ≤ a := by omega
  have hrank : ∀ j, j < Nd d → PRank t (freeAt t d m j) (prankOf t (freeAt t d m j)) := by
    intro j hj
    have hf := freeAt_free t hd m hj
    obtain ⟨r, -, hr⟩ := exists_prank_le_of_inFrame t
      (⟨m, hf.1.le, hf.2.1.le⟩ : InFrame (phaseOffsets t) d (freeAt t d m j))
    exact prankOf_spec ⟨r, hr⟩
  rcases le_or_gt d a with hda | had
  · -- a small board: every zero has even rank, the parity guard rejects it
    refine MachineP.guard_no_halt _ _ (fun j hj0 _ => ?_) i
    have hjN : j < Nd d := by
      by_contra h
      simp [cutH, h] at hj0
    rw [cutH, ite_eq_left hjN, decide_eq_false_iff_not] at hj0
    have hge : 2 * a - 2 ≤ prankOf t (freeAt t d m j) := by omega
    have hev := free_rank_even t ha2 hda m (freeOff_nth t hd m hjN) (hrank j hjN) hge
    rw [cutPi, decide_eq_false_iff_not]
    omega
  · -- a large board: it decodes `n`
    have hU' : ¬ U.HaltsOn (a + 1 - n0 - 1) := by rwa [show a + 1 - n0 - 1 = n by omega]
    refine MachineP.decode_no_halt (a + 1) (by omega) hU' _ _ ?_ i
    set p := FreeOff t d m with hp
    have hcount : Nat.count p (4 ^ a - 2) = 2 ^ (a + 1) - 2 :=
      count_initial_zero t (by omega) had m
    obtain ⟨hfree, hr0, hlt⟩ := initial_zero t ha2 had m
    have hnth : Nat.nth p (2 ^ (a + 1) - 2) = 4 ^ a - 2 := by
      rw [← hcount]; exact Nat.nth_count hfree
    have hjN : 2 ^ (a + 1) - 2 < Nd d := by
      have : 2 ^ (a + 1) < 2 ^ (d + 2) := Nat.pow_lt_pow_right (by norm_num) (by omega)
      show 2 ^ (a + 1) - 2 < 2 ^ (d + 2) - 2
      have : 2 ≤ 2 ^ (a + 1) := Nat.le_self_pow (by omega) 2
      omega
    have hstar : freeAt t d m (2 ^ (a + 1) - 2) =
        rfree (phaseOffsets t) d m + ((4 ^ a - 2 : ℕ) : ℤ) := by
      simp only [freeAt]; rw [← hp, hnth]
    have hr0' : prankOf t (freeAt t d m (2 ^ (a + 1) - 2)) = 2 * a - 1 := by
      rw [hstar]; exact prankOf_eq hr0
    refine ⟨fun j hj => ?_, ?_, ?_⟩
    · have hjN' : j < Nd d := by omega
      have hl : Nat.nth p j < 4 ^ a - 2 := by
        rw [← hnth]
        exact Nat.nth_lt_nth_of_lt_card (freeOff_finite t d m) hj
          (by rw [card_freeOff t hd m]; exact hjN)
      have h3 := hlt _ _ hl (freeOff_nth t hd m hjN') (hrank j hjN')
      rw [cutH, ite_eq_left hjN', decide_eq_true_iff]
      omega
    · rw [cutH, ite_eq_left hjN, hr0', decide_eq_false_iff_not]
      omega
    · rw [cutPi, hr0', decide_eq_true_iff]
      omega

/-- **No board content carries HALT** under the correct cutoff when `U(n)` does not halt. -/
theorem board_run_no_halt {U : UPD.Machine} {n0 n : ℕ} (hn : 1 ≤ n) (hn0 : 1 ≤ n0)
    (hU : ¬ U.HaltsOn n) (t : ℕ → Bool) {cut : ℕ}
    (hcut : cut = 2 * (n + n0) - 2 ∨ cut = 2 * (n + n0) - 1) {d : ℕ} (hd : 1 ≤ d) (m : ℤ)
    (i : ℕ) (j : Fin (Nd d)) :
    MachineP.CarriesHalt U n0 (MachineP.runP U n0 (Nd d) (cutH t d m cut) (cutPi t d m) i j) =
      false := by
  have hN : 1 ≤ Nd d := by
    have : 8 ≤ 2 ^ (d + 2) := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ (d + 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
    show 1 ≤ 2 ^ (d + 2) - 2
    omega
  exact MachineP.runP_no_halt hN _ _ (board_no_halt hn hn0 hU t hcut hd m) i j

end UND.Chart
