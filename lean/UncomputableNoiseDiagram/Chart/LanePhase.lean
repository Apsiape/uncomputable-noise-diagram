/-
# Section 3.2: the lane phase on finite bottom rows (S5, arithmetic part; FD2)

Part of node S5 of `BLUEPRINT.md` (Part A.3), NEW. Paper (Section 3.2): "The lane phase is
`p(x, y) = y - τ₂ - 1 (mod B)` (9). … On a finite bottom row of depth `d`, origins and ends are
respectively `(L_d(z), Bot_d(z'))`, `(R_d(z), Bot_d(z'))` … At this row
`p(Bot_d(z')) ≡ (4z'+1)4^d (mod 4^{min(d+1,k)})`, so the phase-zero gates are exactly the finite
bottom rows with `d ≥ k`."

**Fidelity deviation FD2** (QB, session 3; to be corrected in v1.1.0): the last clause is false as
a global statement about all gates (it is a statement about the gates on finite bottom rows only);
it is formalized in the restricted form, for gates on a finite bottom row of depth `d`
(`lanePhase_bot_eq_zero_iff`).

Conventions (REUSE of the hard-model core's scaffold): the row phase `τ₂ ∈ ℤ₂` has binary digits
`t : ℕ → Bool`; `τ₂ mod 2^l` is `UPD.Scaffold.wsum t l`; the frame offsets are
`a_d = τ₂ mod 4^{d+1} = UPD.Scaffold.phaseOffsets t d`; the lower endpoint of the depth-`d` row frame
number `m` is `Bot_d(m) = UPD.Scaffold.frameLo a d m = a_d + (4m+1)4^d + 1` (7). With `B = 4^k`:

* `lanePhase t k y = (y - τ₂ - 1) mod 4^k` (9), `lanePhase_succ` (it increases by one vertically);
* **`lanePhase_bot`**: `p(Bot_d(m)) ≡ (4m+1)4^d (mod 4^{min(d+1,k)})`;
* **`lanePhase_bot_eq_zero_iff`** (FD2, restricted form): on a finite bottom row of depth `d`,
  `p = 0` iff `d ≥ k`.
-/
import UndecidablePhaseDiagram.Scaffold.Frames
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false

namespace UND.Chart

open UPD.Scaffold

/-- (9): the lane phase `p(x, y) = y - τ₂ - 1 (mod 4^k)`, for a row phase `τ₂` with binary digits
`t` (it does not depend on `x`). -/
def lanePhase (t : ℕ → Bool) (k : ℕ) (y : ℤ) : ℤ := (y - wsum t (2 * k) - 1) % 4 ^ k

/-- The lane phase increases by one vertically. -/
theorem lanePhase_succ (t : ℕ → Bool) (k : ℕ) (y : ℤ) :
    lanePhase t k (y + 1) = (lanePhase t k y + 1) % 4 ^ k := by
  unfold lanePhase
  rw [Int.emod_add_emod]
  ring_nf

theorem four_pow_eq (j : ℕ) : (4 : ℤ) ^ j = 2 ^ (2 * j) := by
  rw [pow_mul]
  norm_num

/-- `τ mod 2^{2l} ≡ τ mod 2^{2j}` modulo `4^j` for `j ≤ l`. -/
theorem wsum_dvd_sub (t : ℕ → Bool) {j l : ℕ} (h : j ≤ l) :
    (4 : ℤ) ^ j ∣ wsum t (2 * l) - wsum t (2 * j) := by
  rw [four_pow_eq]
  have := wsum_emod t (show 2 * j ≤ 2 * l by omega)
  rw [Int.dvd_iff_emod_eq_zero, Int.sub_emod, this, Int.emod_eq_of_lt (wsum_nonneg t _)
    (wsum_lt t _), sub_self, Int.zero_emod]

/-- **§3.2: `p(Bot_d(m)) ≡ (4m+1)4^d (mod 4^{min(d+1,k)})`.** -/
theorem lanePhase_bot (t : ℕ → Bool) (k d : ℕ) (m : ℤ) :
    lanePhase t k (frameLo (phaseOffsets t) d m) % 4 ^ (min (d + 1) k) =
      ((4 * m + 1) * 4 ^ d) % 4 ^ (min (d + 1) k) := by
  set j := min (d + 1) k with hj
  have hjk : (4 : ℤ) ^ j ∣ 4 ^ k := pow_dvd_pow 4 (min_le_right _ _)
  have h1 := wsum_dvd_sub t (show j ≤ d + 1 from min_le_left _ _)
  have h2 := wsum_dvd_sub t (show j ≤ k from min_le_right _ _)
  unfold lanePhase
  rw [Int.emod_emod_of_dvd _ hjk]
  have e : frameLo (phaseOffsets t) d m - wsum t (2 * k) - 1 =
      (4 * m + 1) * 4 ^ d + ((wsum t (2 * (d + 1)) - wsum t (2 * j)) -
        (wsum t (2 * k) - wsum t (2 * j))) := by
    simp only [frameLo, phaseOffsets]
    ring_nf
  rw [e, Int.add_emod, Int.emod_eq_zero_of_dvd (dvd_sub h1 h2), add_zero, Int.emod_emod_of_dvd]
  exact dvd_refl _

/-- **§3.2, restricted form (FD2)**: on a finite bottom row of depth `d`, the lane phase is zero iff
`d ≥ k`. -/
theorem lanePhase_bot_eq_zero_iff (t : ℕ → Bool) (k d : ℕ) (m : ℤ) :
    lanePhase t k (frameLo (phaseOffsets t) d m) = 0 ↔ k ≤ d := by
  have hb := lanePhase_bot t k d m
  have hpos : (0 : ℤ) < 4 ^ k := by positivity
  have hrange : 0 ≤ lanePhase t k (frameLo (phaseOffsets t) d m) ∧
      lanePhase t k (frameLo (phaseOffsets t) d m) < 4 ^ k :=
    ⟨Int.emod_nonneg _ hpos.ne', Int.emod_lt_of_pos _ hpos⟩
  constructor
  · intro h0
    by_contra hlt
    push Not at hlt
    have hmin : min (d + 1) k = d + 1 := min_eq_left (by omega)
    rw [hmin, h0, Int.zero_emod] at hb
    have e : (4 * m + 1) * 4 ^ d = 4 ^ d + m * 4 ^ (d + 1) := by ring
    rw [e, Int.add_mul_emod_self_right] at hb
    have h4 : (0 : ℤ) < 4 ^ d := by positivity
    have h4' : (4 : ℤ) ^ d < 4 ^ (d + 1) := by
      rw [pow_succ]
      linarith
    rw [Int.emod_eq_of_lt h4.le h4'] at hb
    linarith
  · intro hkd
    have hmin : min (d + 1) k = k := min_eq_right (by omega)
    rw [hmin, Int.emod_eq_of_lt hrange.1 hrange.2] at hb
    rw [hb]
    exact Int.emod_eq_zero_of_dvd (Dvd.dvd.mul_left (pow_dvd_pow 4 hkd) _)

end UND.Chart
