/-
# The intervals (17) and their statement-level properties

Leaves of Part A.9 of `BLUEPRINT.md` (the last paragraph of the proof of Theorem 9.3):
* `ell d = ℓ_d = 2·4^d - 1` (Section 3.2, the ruler length) and `ℓ_{d+1} = 4 ℓ_d + 3`;
* the intervals (17), `I_n = (2C/ℓ_a, 21C/(10 ℓ_a))`, `a = n + n₀`, for `C = 1/c` with a positive
  natural number `c` (in the paper `c = (128 K_mem)²`, (24));
* **`isWindowFamily_windows`**: for every `c ≥ 1` and every `n₀` they are "nonempty rational open
  intervals computable from `n`", inside `(0, 1)`, and pairwise disjoint
  ("Since `ℓ_{a+1} = 4ℓ_a + 3`, the upper endpoint for `a + 1` lies below the lower endpoint for
  `a`"). The search for `n₀` (28) is not needed here: the statement holds for every `n₀`.
-/
import UncomputableNoiseDiagram.Statements
import Mathlib.Computability.Primrec.Basic

set_option autoImplicit false

namespace UND.Windows

/-- Section 3.2: `ℓ_d = R_d - L_d = 2·4^d - 1`. -/
def ell (d : ℕ) : ℕ := 2 * 4 ^ d - 1

theorem ell_add_one (d : ℕ) : ell d + 1 = 2 * 4 ^ d := by
  have : 1 ≤ 4 ^ d := Nat.one_le_pow _ _ (by norm_num)
  unfold ell; omega

theorem ell_pos (d : ℕ) : 0 < ell d := by
  have : 1 ≤ 4 ^ d := Nat.one_le_pow _ _ (by norm_num)
  unfold ell; omega

/-- Proof of Theorem 9.3: `ℓ_{a+1} = 4 ℓ_a + 3`. -/
theorem ell_succ (d : ℕ) : ell (d + 1) = 4 * ell d + 3 := by
  have h := ell_add_one d
  have h' := ell_add_one (d + 1)
  rw [pow_succ] at h'
  omega

theorem ell_mono {d e : ℕ} (h : d ≤ e) : ell d ≤ ell e := by
  have h1 := ell_add_one d
  have h2 := ell_add_one e
  have : 4 ^ d ≤ 4 ^ e := Nat.pow_le_pow_right (by norm_num) h
  omega

theorem seven_le_ell {d : ℕ} (hd : 1 ≤ d) : 7 ≤ ell d := by
  have := ell_mono hd
  have h1 : ell 1 = 7 := by decide
  omega

/-- (17): the lower endpoint `2C/ℓ_{n+n₀}` with `C = 1/c`. -/
def lo (c n0 n : ℕ) : ℚ := 2 / ((c : ℚ) * ell (n + n0))

/-- (17): the upper endpoint `21C/(10 ℓ_{n+n₀})` with `C = 1/c`. -/
def hi (c n0 n : ℕ) : ℚ := 21 / (10 * (c : ℚ) * ell (n + n0))

/-- The presentation `(2, c ℓ_{n+n₀})` of the lower endpoint. -/
def loP (c n0 n : ℕ) : ℕ × ℕ := (2, c * ell (n + n0))

/-- The presentation `(21, 10 c ℓ_{n+n₀})` of the upper endpoint. -/
def hiP (c n0 n : ℕ) : ℕ × ℕ := (21, 10 * c * ell (n + n0))

theorem primrec_ell : Primrec ell := by
  have hpow : Primrec₂ ((· ^ ·) : ℕ → ℕ → ℕ) := Primrec₂.unpaired'.1 Nat.Primrec.pow
  have h : Primrec fun d : ℕ => 4 ^ d := hpow.comp (Primrec.const 4) Primrec.id
  exact Primrec.nat_sub.comp (Primrec.nat_mul.comp (Primrec.const 2) h) (Primrec.const 1)

theorem computable_loP (c n0 : ℕ) : Computable (loP c n0) := by
  have h : Primrec fun n : ℕ => c * ell (n + n0) :=
    Primrec.nat_mul.comp (Primrec.const c)
      (primrec_ell.comp (Primrec.nat_add.comp Primrec.id (Primrec.const n0)))
  exact (Primrec.pair (Primrec.const 2) h).to_comp

theorem computable_hiP (c n0 : ℕ) : Computable (hiP c n0) := by
  have h : Primrec fun n : ℕ => 10 * c * ell (n + n0) :=
    Primrec.nat_mul.comp (Primrec.const (10 * c))
      (primrec_ell.comp (Primrec.nat_add.comp Primrec.id (Primrec.const n0)))
  exact (Primrec.pair (Primrec.const 21) h).to_comp

theorem presents_lo (c n0 n : ℕ) (hc : 1 ≤ c) : Presents (loP c n0 n) (lo c n0 n) := by
  refine ⟨Nat.mul_pos (by omega) (ell_pos _), ?_⟩
  simp [loP, lo]

theorem presents_hi (c n0 n : ℕ) (hc : 1 ≤ c) : Presents (hiP c n0 n) (hi c n0 n) := by
  refine ⟨Nat.mul_pos (by omega) (ell_pos _), ?_⟩
  simp [hiP, hi, mul_assoc]

/-- For `a < b`: `21 ℓ_a < 20 ℓ_b` (`ℓ_b ≥ ℓ_{a+1} = 4ℓ_a + 3`). -/
theorem ell_gap {a b : ℕ} (h : a < b) : 21 * ell a < 20 * ell b := by
  have h1 := ell_mono (Nat.succ_le_of_lt h)
  rw [ell_succ] at h1
  omega

/-- For `n < n'`: the upper endpoint of `I_{n'}` lies below the lower endpoint of `I_n`. -/
theorem hi_lt_lo (c n0 : ℕ) (hc : 1 ≤ c) {n n' : ℕ} (h : n < n') :
    hi c n0 n' < lo c n0 n := by
  have hcq : (0 : ℚ) < c := by exact_mod_cast hc
  have ha : (0 : ℚ) < ell (n + n0) := by exact_mod_cast ell_pos _
  have hb : (0 : ℚ) < ell (n' + n0) := by exact_mod_cast ell_pos _
  have hg : (21 : ℚ) * ell (n + n0) < 20 * ell (n' + n0) := by
    exact_mod_cast ell_gap (by omega : n + n0 < n' + n0)
  unfold hi lo
  rw [div_lt_div_iff₀ (by positivity) (by positivity)]
  nlinarith

/-- **The intervals (17) form a window family** (statement-level clauses of Theorem 9.3): for
every `c ≥ 1` and every `n₀`, they are nonempty open intervals of rates in `(0, 1)` with
computably presented rational endpoints, pairwise disjoint for distinct `n, n' ≥ 1`. -/
theorem isWindowFamily_windows (c n0 : ℕ) (hc : 1 ≤ c) : IsWindowFamily (lo c n0) (hi c n0) := by
  have hcq : (1 : ℚ) ≤ c := by exact_mod_cast hc
  refine ⟨⟨loP c n0, computable_loP c n0, fun n => presents_lo c n0 n hc⟩,
    ⟨hiP c n0, computable_hiP c n0, fun n => presents_hi c n0 n hc⟩, ?_, ?_⟩
  · intro n hn
    have h7 : (7 : ℚ) ≤ ell (n + n0) := by exact_mod_cast seven_le_ell (by omega)
    have hpos : (0 : ℚ) < (c : ℚ) * ell (n + n0) := by positivity
    refine ⟨by unfold lo; positivity, ?_, ?_⟩
    · unfold lo hi
      rw [div_lt_div_iff₀ hpos (by positivity)]
      nlinarith
    · unfold hi
      rw [div_lt_one (by positivity)]
      nlinarith
  · intro n n' _ _ hne
    rcases lt_or_gt_of_ne hne with h | h
    · rw [Set.disjoint_iff]
      rintro x ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      have := hi_lt_lo c n0 hc h
      have : ((hi c n0 n' : ℚ) : ℝ) < (lo c n0 n : ℝ) := by exact_mod_cast this
      linarith
    · rw [Set.disjoint_iff]
      rintro x ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩
      have := hi_lt_lo c n0 hc h
      have : ((hi c n0 n : ℚ) : ℝ) < (lo c n0 n' : ℝ) := by exact_mod_cast this
      linarith

end UND.Windows
