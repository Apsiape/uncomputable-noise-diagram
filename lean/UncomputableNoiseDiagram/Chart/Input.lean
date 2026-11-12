/-
# Lemma 4.2: which input is read (M4)

Node M4 of `BLUEPRINT.md` (Part A.4), NEW (template: the hard-model core's
`UPD.Scaffold.isFree_iff_allowed`, `Allowed`, `sum_allowed`, `card_free`).

Paper (Lemma 4.2): "Suppose `a ≥ 2` and the finite-rank flags satisfy `b_{2a-3} = 1`,
`b_{2a-1} = 0`. Every depth-`d` board with `d > a` has its initial zero at logical index
`2^{a+1} - 2`, with odd parent rank `2a - 1`. A board with `d ≤ a` either has no zero before its
boundary or has a zero with even rank before any odd-rank zero. Thus it cannot simulate a different
input." Proof: "In a depth-`d` frame of phase `τ_i`, write a free coordinate as
`a_d + (4z+1)4^d + t`, starting with `t = 2`. In its left half, before `t = 4^d`, the parent rank is
`ν₂(⌊t/2⌋)`. An even rank `2e`, `1 ≤ e < d`, gives residues `2·4^e` or `2·4^e + 1` inside a smaller
excluded frame. Hence noncentral free ranks are zero or odd. The two central coordinates have rank
`2d`. For `d > a`, the initial free coordinate of rank at least `2a - 2` is `t = 4^a`, of rank
`2a - 1`. … `|A_a| = 2^{a+1}`. Allowed coordinates in `[2, 4^a]` remove zero and one and add `4^a`,
giving `2^{a+1} - 1` coordinates. The initial zero index is one less. If `d < a - 1`, all board
ranks are below the cutoff. If `d = a - 1` an initial zero can occur only at the even central rank
`2a - 2`; if `d = a` it again occurs at the even centre. The parity guard rejects these cases. This
uses only relative finite residues and holds in every phase."

Formalization: a free coordinate of the frame `I_d(m)` is `r_d(m) + n` (`rfree`, the paper's
`t = n + 2`), in every phase.
* `prank_of_half`: the parent rank from the half-offset `(y - a_d)/2`;
* **`prank_left`** (`ν₂(⌊t/2⌋)` before `t = 4^d`), **`prank_center`** (`2d` at `t = 4^d, 4^d+1`),
  **`prank_right`** (`ν₂(⌊(t - 4^d)/2⌋)` after the centre);
* `not_isFree_of_mod`, **`free_left_rank`**, **`free_right_rank`** (noncentral free ranks are zero or
  odd, and at most `2d - 3`);
* **`free_rank_even`** (`d ≤ a`: every free rank `≥ 2a - 2` is even, the central `2d`);
* **`initial_zero`** (`d > a`: `t = 4^a` is free of rank `2a - 1`, earlier free coordinates have
  rank `≤ 2a - 3`), **`count_initial_zero`** (its index is `2^{a+1} - 2`);
* `chi2_eq` (`χ₂` is the parity of the row's parent rank, every phase);
* **`input_read_large`**, **`input_read_small`**: Lemma 4.2 on a legal decorated chart in every
  phase, with the cutoff of Lemma 3.2.
-/
import UncomputableNoiseDiagram.Chart.Decorated
import Mathlib.Data.Nat.Nth
import Mathlib.Data.Nat.Factorization.Basic

set_option autoImplicit false

namespace UND.Chart

open UPD UPD.Scaffold

/-! ## Ranks of free coordinates -/

/-- The parent rank from the half-offset: if `(y - a_d)/2 = A·2^{k+1} + 2^k(2o+1)` with
`k ≤ 2d`, then `y` has parent rank `k`. -/
theorem prank_of_half (t : ℕ → Bool) (d : ℕ) (y : ℤ) {k : ℕ} (hk : k ≤ 2 * d) (A o : ℤ)
    (h : (y - phaseOffsets t d) / 2 = A * 2 ^ (k + 1) + 2 ^ k * (2 * o + 1)) : PRank t y k := by
  have ha : phaseOffsets t d = bitZ (t 0) + 2 * wsum (fun m => t (m + 1)) (2 * d + 1) := rfl
  unfold PRank
  apply isRank_of_emod (l := 2 * d + 1) (by omega)
  have e : (y - bitZ (t 0)) / 2 - wsum (fun m => t (m + 1)) (2 * d + 1) =
      (y - phaseOffsets t d) / 2 := by rw [ha]; omega
  rw [e, h]
  have h2 : (0 : ℤ) < 2 ^ k := by positivity
  rw [show A * 2 ^ (k + 1) + 2 ^ k * (2 * o + 1) = 2 ^ k + 2 ^ (k + 1) * (A + o) by ring,
    Int.add_mul_emod_self_left, Int.emod_eq_of_lt h2.le (by rw [pow_succ]; linarith)]

theorem rfree_sub (t : ℕ → Bool) (d : ℕ) (m : ℤ) (n : ℕ) :
    rfree (phaseOffsets t) d m + n - phaseOffsets t d = (4 * m + 1) * 4 ^ d + ((n : ℤ) + 2) := by
  simp only [rfree, frameLo]; ring

theorem two_pow_succ_le {N k o : ℕ} (hs : N / 2 = 2 ^ k * (2 * o + 1)) : 2 ^ (k + 1) ≤ N := by
  have : 2 ^ k ≤ 2 ^ k * (2 * o + 1) := Nat.le_mul_of_pos_right _ (by omega)
  rw [pow_succ]; omega

theorem four_pow_eq_two_pow_mul (b : ℕ) : (4 : ℕ) ^ b = 2 ^ (2 * b) := by
  rw [pow_mul]; norm_num

theorem add_two_le_of_two_pow {k b N : ℕ} (h1 : 2 ^ (k + 1) ≤ N) (h2 : N < 4 ^ b) :
    k + 2 ≤ 2 * b := by
  rw [four_pow_eq_two_pow_mul] at h2
  have := (pow_lt_pow_iff_right₀ (by norm_num : (1 : ℕ) < 2)).1 (lt_of_le_of_lt h1 h2)
  omega

/-- `4^d = 2·2^{k+1}·2^j` when `2d = k + 2 + j`. -/
theorem four_pow_split {d k j : ℕ} (hj : 2 * d = k + 2 + j) :
    (4 : ℤ) ^ d = 2 * (2 ^ (k + 1) * 2 ^ j) := by
  rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul, hj]; ring

/-- **Lemma 4.2, left half**: before the centre (`t = n + 2 < 4^d`), the free-frame coordinate
`r_d(m) + n` has parent rank `ν₂(⌊t/2⌋)`, in every phase. -/
theorem prank_left (t : ℕ → Bool) {d : ℕ} (m : ℤ) {n k o : ℕ} (hn : n + 2 < 4 ^ d)
    (hs : (n + 2) / 2 = 2 ^ k * (2 * o + 1)) :
    PRank t (rfree (phaseOffsets t) d m + n) k := by
  have hk := add_two_le_of_two_pow (two_pow_succ_le hs) hn
  obtain ⟨j, hj⟩ : ∃ j, 2 * d = k + 2 + j := ⟨2 * d - (k + 2), by omega⟩
  refine prank_of_half t d _ (by omega) ((4 * m + 1) * 2 ^ j) o ?_
  rw [rfree_sub, four_pow_split hj]
  have hs' : ((n : ℤ) + 2) / 2 = 2 ^ k * (2 * o + 1) := by
    have : (((n + 2) / 2 : ℕ) : ℤ) = ((n : ℤ) + 2) / 2 := by omega
    rw [← this, hs]; push_cast; ring
  rw [show (4 * m + 1) * (2 * (2 ^ (k + 1) * 2 ^ j)) + ((n : ℤ) + 2) =
      2 * ((4 * m + 1) * 2 ^ j * 2 ^ (k + 1)) + ((n : ℤ) + 2) by ring,
    show ∀ X : ℤ, (2 * X + ((n : ℤ) + 2)) / 2 = X + ((n : ℤ) + 2) / 2 from fun X => by omega, hs']

/-- **Lemma 4.2, the centre**: the two central coordinates `t = 4^d, 4^d + 1` have parent rank
`2d`, in every phase. -/
theorem prank_center (t : ℕ → Bool) (d : ℕ) (m : ℤ) {n : ℕ}
    (hn : n + 2 = 4 ^ d ∨ n + 2 = 4 ^ d + 1) :
    PRank t (rfree (phaseOffsets t) d m + n) (2 * d) := by
  refine prank_of_half t d _ le_rfl 0 m ?_
  rw [rfree_sub]
  have e4 : (4 : ℤ) ^ d = 2 ^ (2 * d) := by
    rw [show (4 : ℤ) = 2 ^ 2 by norm_num, ← pow_mul]
  have key : ∀ σ : ℤ, 0 ≤ σ → σ ≤ 1 → ((4 * m + 1) * 2 ^ (2 * d) + (2 ^ (2 * d) + σ)) / 2 =
      0 * 2 ^ (2 * d + 1) + 2 ^ (2 * d) * (2 * m + 1) := by
    intro σ h0 h1
    rw [show (4 * m + 1) * 2 ^ (2 * d) + (2 ^ (2 * d) + σ) =
      2 * (2 ^ (2 * d) * (2 * m + 1)) + σ by ring]
    generalize 2 ^ (2 * d) * (2 * m + 1) = Z
    omega
  rcases hn with h | h
  · have h' : (n : ℤ) + 2 = 2 ^ (2 * d) + 0 := by rw [← e4, add_zero]; exact_mod_cast h
    rw [e4, h']
    exact key 0 le_rfl zero_le_one
  · have h' : (n : ℤ) + 2 = 2 ^ (2 * d) + 1 := by rw [← e4]; exact_mod_cast h
    rw [e4, h']
    exact key 1 zero_le_one le_rfl

/-- **Lemma 4.2, right half**: after the centre (`t = n + 2 = 4^d + t'`, `2 ≤ t' < 4^d`), the
parent rank is `ν₂(⌊t'/2⌋)`, in every phase. -/
theorem prank_right (t : ℕ → Bool) {d : ℕ} (m : ℤ) {n t' k o : ℕ} (ht : n + 2 = 4 ^ d + t')
    (ht' : t' < 4 ^ d) (hs : t' / 2 = 2 ^ k * (2 * o + 1)) :
    PRank t (rfree (phaseOffsets t) d m + n) k := by
  have hk := add_two_le_of_two_pow (two_pow_succ_le hs) ht'
  obtain ⟨j, hj⟩ : ∃ j, 2 * d = k + 2 + j := ⟨2 * d - (k + 2), by omega⟩
  refine prank_of_half t d _ (by omega) ((2 * m + 1) * 2 * 2 ^ j) o ?_
  have htZ : (n : ℤ) + 2 = 4 ^ d + t' := by exact_mod_cast ht
  have hs' : (t' : ℤ) / 2 = 2 ^ k * (2 * o + 1) := by
    have : ((t' / 2 : ℕ) : ℤ) = (t' : ℤ) / 2 := by omega
    rw [← this, hs]; push_cast; ring
  rw [rfree_sub, htZ, show (4 * m + 1) * 4 ^ d + (4 ^ d + (t' : ℤ)) =
      2 * ((2 * m + 1) * 4 ^ d) + t' by ring,
    show ∀ X : ℤ, (2 * X + (t' : ℤ)) / 2 = X + (t' : ℤ) / 2 from fun X => by omega, hs',
    four_pow_split hj]
  ring

/-! ## Even ranks are excluded off the centre -/

/-- `(2·4^e(2o+1) + σ + 4^{e+1}X) mod 4^{e+1} = 2·4^e + σ` for `σ ≤ 1`. -/
theorem mod_of_odd_block {N e o σ X : ℕ} (hσ : σ ≤ 1)
    (hN : N = 2 * (2 ^ (2 * e) * (2 * o + 1)) + σ + 4 ^ (e + 1) * X) :
    N % 4 ^ (e + 1) = 2 * 4 ^ e + σ := by
  subst hN
  rw [← four_pow_eq_two_pow_mul, Nat.add_mul_mod_self_left]
  have hp : 1 ≤ 4 ^ e := Nat.one_le_pow _ _ (by norm_num)
  rw [show 2 * (4 ^ e * (2 * o + 1)) + σ = (2 * 4 ^ e + σ) + 4 ^ (e + 1) * o by
      rw [pow_succ]; ring,
    Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt (by rw [pow_succ]; omega)]

/-- A coordinate of the interior of `I_d(m)` with residue `2·4^e + σ (mod 4^{e+1})`, `1 ≤ e < d`,
lies in a smaller frame, so it is not free. -/
theorem not_isFree_of_mod {t : ℕ → Bool} {d e : ℕ} (he : 1 ≤ e) (hed : e < d) (m : ℤ) {n : ℕ}
    (hn : n + 2 < 2 * 4 ^ d) {σ : ℕ} (hσ : σ ≤ 1) (h : (n + 2) % 4 ^ (e + 1) = 2 * 4 ^ e + σ) :
    ¬ IsFree (phaseOffsets t) d m (rfree (phaseOffsets t) d m + n) := by
  rw [isFree_iff_allowed (frameOffsets_phase t) m hn]
  intro hA
  apply hA e he hed
  rw [Nat.mod_mod_of_dvd _ (pow_dvd_pow 4 hed), h]
  have hp : 1 ≤ 4 ^ e := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- **Noncentral free ranks, left half**: zero or odd, and at most `2b - 3` when `t < 4^b`
(`b ≤ d`). -/
theorem free_left_rank {t : ℕ → Bool} {d b : ℕ} (hbd : b ≤ d) (m : ℤ) {n k o : ℕ}
    (hn : n + 2 < 4 ^ b) (hs : (n + 2) / 2 = 2 ^ k * (2 * o + 1))
    (hfree : IsFree (phaseOffsets t) d m (rfree (phaseOffsets t) d m + n)) :
    k = 0 ∨ (k % 2 = 1 ∧ k + 3 ≤ 2 * b) := by
  have hk := add_two_le_of_two_pow (two_pow_succ_le hs) hn
  rcases Nat.even_or_odd k with ⟨e, he⟩ | ho
  · by_cases he0 : e = 0
    · left; omega
    · exfalso
      have hbd' : 4 ^ b ≤ 4 ^ d := Nat.pow_le_pow_right (by norm_num) hbd
      refine not_isFree_of_mod (t := t) (e := e) (by omega) (by omega) m (n := n) (by omega)
        (σ := (n + 2) % 2) (by omega) (mod_of_odd_block (o := o) (X := 0) (by omega) ?_) hfree
      rw [mul_zero, add_zero, show 2 * e = k by omega, ← hs]
      omega
  · right
    obtain ⟨j, hj⟩ := ho
    omega

/-- **Noncentral free ranks, right half**: zero or odd, and at most `2d - 3`. -/
theorem free_right_rank {t : ℕ → Bool} {d : ℕ} (m : ℤ) {n t' k o : ℕ} (ht : n + 2 = 4 ^ d + t')
    (ht' : t' < 4 ^ d) (hs : t' / 2 = 2 ^ k * (2 * o + 1))
    (hfree : IsFree (phaseOffsets t) d m (rfree (phaseOffsets t) d m + n)) :
    k = 0 ∨ (k % 2 = 1 ∧ k + 3 ≤ 2 * d) := by
  have hk := add_two_le_of_two_pow (two_pow_succ_le hs) ht'
  rcases Nat.even_or_odd k with ⟨e, he⟩ | ho
  · by_cases he0 : e = 0
    · left; omega
    · exfalso
      obtain ⟨X, hX⟩ : 4 ^ (e + 1) ∣ 4 ^ d := pow_dvd_pow 4 (by omega)
      refine not_isFree_of_mod (t := t) (e := e) (by omega) (by omega) m (n := n) (by omega)
        (σ := t' % 2) (by omega) (mod_of_odd_block (o := o) (X := X) (by omega) ?_) hfree
      rw [ht, ← hX, show 2 * e = k by omega, ← hs]
      omega
  · right
    obtain ⟨j, hj⟩ := ho
    omega

/-- Every `s ≥ 1` is `2^k(2o+1)`. -/
theorem exists_two_pow_mul_odd {s : ℕ} (hs : s ≠ 0) : ∃ k o : ℕ, s = 2 ^ k * (2 * o + 1) := by
  obtain ⟨k, o', ho, h⟩ := Nat.exists_eq_two_pow_mul_odd hs
  obtain ⟨o, rfl⟩ := ho
  exact ⟨k, o, h⟩

/-- A free coordinate `r_d(m) + n` of `I_d(m)` has `n + 2 < 2·4^d`. -/
theorem lt_of_isFree {t : ℕ → Bool} {d : ℕ} {m : ℤ} {n : ℕ}
    (h : IsFree (phaseOffsets t) d m (rfree (phaseOffsets t) d m + n)) : n + 2 < 2 * 4 ^ d := by
  have h2 := h.2.1
  simp only [rfree, frameLo, frameHi] at h2
  have : (n : ℤ) + 2 < 2 * 4 ^ d := by linarith
  exact_mod_cast this

/-- **Lemma 4.2, `d ≤ a`**: in a depth-`d` frame with `1 ≤ d ≤ a`, `a ≥ 2`, every free coordinate
of parent rank at least `2a - 2` has even rank (it is a central coordinate, of rank `2d`), in
every phase. -/
theorem free_rank_even (t : ℕ → Bool) {a d : ℕ} (ha : 2 ≤ a) (hda : d ≤ a) (m : ℤ) {n r : ℕ}
    (hfree : IsFree (phaseOffsets t) d m (rfree (phaseOffsets t) d m + n))
    (hr : PRank t (rfree (phaseOffsets t) d m + n) r) (hra : 2 * a - 2 ≤ r) : r % 2 = 0 := by
  have hlt := lt_of_isFree hfree
  rcases lt_or_ge (n + 2) (4 ^ d) with h1 | h1
  · obtain ⟨k, o, hs⟩ := exists_two_pow_mul_odd (s := (n + 2) / 2) (by omega)
    have hk : r = k := hr.unique (prank_left t m h1 hs)
    rcases free_left_rank le_rfl m h1 hs hfree with h | ⟨-, h⟩ <;> omega
  · rcases lt_or_ge (n + 2) (4 ^ d + 2) with h2 | h2
    · have hc := prank_center t d m (n := n) (by omega)
      have := hr.unique hc
      omega
    · obtain ⟨t', ht⟩ : ∃ t', n + 2 = 4 ^ d + t' := ⟨n + 2 - 4 ^ d, by omega⟩
      obtain ⟨k, o, hs⟩ := exists_two_pow_mul_odd (s := t' / 2) (by omega)
      have hk : r = k := hr.unique (prank_right t m ht (by omega) hs)
      rcases free_right_rank m ht (by omega) hs hfree with h | ⟨-, h⟩ <;> omega

/-! ## The initial zero of a large board -/

/-- For `s < 4^a` and `a ≤ d`, the depth-`d` and depth-`a` allowance agree. -/
theorem allowed_lift {a d s : ℕ} (had : a ≤ d) (hs : s < 4 ^ a) : Allowed d s ↔ Allowed a s := by
  constructor
  · intro h e he hea
    exact h e he (by omega)
  · intro h e he hed
    by_cases hea : e < a
    · exact h e he hea
    · have h1 : 4 ^ a ≤ 4 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
      have h2 : s % 4 ^ (e + 1) = s := Nat.mod_eq_of_lt (by rw [pow_succ]; omega)
      rw [h2]
      omega

/-- `4^a` is allowed at every depth. -/
theorem allowed_four_pow (a d : ℕ) : Allowed d (4 ^ a) := by
  intro e he hed hmod
  by_cases hea : e + 1 ≤ a
  · rw [Nat.mod_eq_zero_of_dvd (pow_dvd_pow 4 hea)] at hmod
    omega
  · have h1 : 4 ^ a ≤ 4 ^ e := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h2 : 4 ^ a % 4 ^ (e + 1) = 4 ^ a := Nat.mod_eq_of_lt (by rw [pow_succ]; omega)
    rw [h2] at hmod
    omega

/-- **Lemma 4.2, `d > a`**: the free coordinate `t = 4^a` (`n = 4^a - 2`) of a depth-`d` frame has
odd parent rank `2a - 1`, and every earlier free coordinate has rank at most `2a - 3`; in every
phase. -/
theorem initial_zero (t : ℕ → Bool) {a d : ℕ} (ha : 2 ≤ a) (had : a < d) (m : ℤ) :
    IsFree (phaseOffsets t) d m (rfree (phaseOffsets t) d m + (4 ^ a - 2 : ℕ)) ∧
    PRank t (rfree (phaseOffsets t) d m + (4 ^ a - 2 : ℕ)) (2 * a - 1) ∧
    ∀ n r : ℕ, n < 4 ^ a - 2 → IsFree (phaseOffsets t) d m (rfree (phaseOffsets t) d m + n) →
      PRank t (rfree (phaseOffsets t) d m + n) r → r + 3 ≤ 2 * a := by
  have h16 : 16 ≤ 4 ^ a := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ 4 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  have had' : 4 ^ a < 4 ^ d := Nat.pow_lt_pow_right (by norm_num) had
  refine ⟨?_, ?_, ?_⟩
  · rw [isFree_iff_allowed (frameOffsets_phase t) m (by omega), show 4 ^ a - 2 + 2 = 4 ^ a by omega,
      Nat.mod_eq_of_lt had']
    exact allowed_four_pow a d
  · refine prank_left t m (o := 0) (by omega) ?_
    rw [show 4 ^ a - 2 + 2 = 4 ^ a by omega, four_pow_eq_two_pow_mul,
      show 2 * a = 2 * a - 1 + 1 by omega, pow_succ]
    simp
  · intro n r hn hfree hr
    obtain ⟨k, o, hs⟩ := exists_two_pow_mul_odd (s := (n + 2) / 2) (by omega)
    have hk : r = k := hr.unique (prank_left t m (by omega) hs)
    rcases free_left_rank (b := a) had.le m (by omega) hs hfree with h | ⟨-, h⟩ <;> omega

open Classical in
/-- **Lemma 4.2, the index of the initial zero**: in a depth-`d` frame with `d > a ≥ 1`, exactly
`2^{a+1} - 2` free coordinates precede `t = 4^a` (`|A_a| = 2^{a+1}` allowed residues, less `0` and
`1`). -/
theorem count_initial_zero (t : ℕ → Bool) {a d : ℕ} (ha : 1 ≤ a) (had : a < d) (m : ℤ) :
    Nat.count (fun n => IsFree (phaseOffsets t) d m (rfree (phaseOffsets t) d m + n))
      (4 ^ a - 2) = 2 ^ (a + 1) - 2 := by
  have h4 : 4 ≤ 4 ^ a := le_self_pow₀ (by norm_num) (by omega)
  have had' : 4 ^ a < 4 ^ d := Nat.pow_lt_pow_right (by norm_num) had
  rw [Nat.count_eq_card_filter_range, Finset.card_filter]
  have hc : ∀ n ∈ Finset.range (4 ^ a - 2),
      (if IsFree (phaseOffsets t) d m (rfree (phaseOffsets t) d m + n) then 1 else 0) =
        ind (Allowed a (2 + n)) := by
    intro n hn
    have hn' := Finset.mem_range.1 hn
    unfold ind
    refine if_congr ?_ rfl rfl
    rw [isFree_iff_allowed (frameOffsets_phase t) m (by omega), Nat.mod_eq_of_lt (by omega),
      allowed_lift had.le (by omega), add_comm]
  rw [Finset.sum_congr rfl hc]
  have hall := sum_allowed ha
  rw [show 4 ^ a = 2 + (4 ^ a - 2) by omega, Finset.sum_range_add] at hall
  have h01 : ∑ n ∈ Finset.range 2, ind (Allowed a n) = 2 := by
    rw [Finset.sum_range_succ, Finset.sum_range_succ, Finset.sum_range_zero]
    simp [ind, allowed_of_le_one (d := a) (zero_le_one), allowed_of_le_one (d := a) (le_refl 1)]
  rw [h01] at hall
  omega

/-! ## Lemma 4.2 on a legal decorated chart -/

/-- `χ₂` is the parity of the row's parent rank (`app:rank-bits`), in every phase. -/
theorem chi2_eq {Z : Plane → DQuarter} {τ : ℕ → Bool × Bool}
    (hτ : IsQPhase (fun ξ => (Z ξ).toQ) τ) (ξ : Plane) {r : ℕ} (hr : PRank (row τ) ξ.2 r) :
    (Z ξ).parent.1.a.1.b2 = decide (r % 2 = 1) := by
  obtain ⟨f, -, hYf, F, hF, hF0⟩ := hτ
  have hpar : (Z ξ).parent.1.a.1 = F 0 (half (ξ - bvec (τ 0))) := by
    have e := congrArg (fun q : Quarter => q.parent.1) (congrFun hYf ξ)
    rw [hF0]
    exact e
  rw [hpar]
  exact rank_bits_row (hF.towerRel (r + 1)) (Nat.lt_succ_self r) hr

/-- The cutoff of Lemma 3.2 with `b_{2a-3} = 1`, `b_{2a-1} = 0`, read from two rows. -/
theorem cutoff_of_flags {Z : Plane → DQuarter} (hZ : IsDTiling Z) {τ : ℕ → Bool × Bool}
    (hτ : IsQPhase (fun ξ => (Z ξ).toQ) τ) {a : ℕ} {ξ₁ ξ₀ : Plane}
    (h₁ : PRank (row τ) ξ₁.2 (2 * a - 3)) (hH₁ : (Z ξ₁).H = true)
    (h₀ : PRank (row τ) ξ₀.2 (2 * a - 1)) (hH₀ : (Z ξ₀).H = false) :
    ∃ b : ℕ → Bool, Antitone b ∧ b (2 * a - 3) = true ∧ b (2 * a - 1) = false ∧
      ∀ ξ s, PRank (row τ) ξ.2 s → (Z ξ).H = b s := by
  obtain ⟨b, hb, -, hbr⟩ := cutoff_of_dtiling hZ hτ
  exact ⟨b, hb, by rw [← hbr ξ₁ _ h₁, hH₁], by rw [← hbr ξ₀ _ h₀, hH₀], hbr⟩

/-- **Lemma 4.2, `d > a`, on a legal decorated chart** (every phase): with the cutoff
`b_{2a-3} = 1`, `b_{2a-1} = 0`, on every column of a depth-`d` row frame, `H_row = 1` at every free
coordinate before `t = 4^a`, and `H_row = 0`, `χ₂ = 1` at `t = 4^a` (the initial zero, of index
`2^{a+1} - 2` by `count_initial_zero`). -/
theorem input_read_large {Z : Plane → DQuarter} {τ : ℕ → Bool × Bool}
    (hτ : IsQPhase (fun ξ => (Z ξ).toQ) τ) {b : ℕ → Bool} (hb : Antitone b) {a d : ℕ}
    (ha : 2 ≤ a) (had : a < d) (h1 : b (2 * a - 3) = true) (h0 : b (2 * a - 1) = false)
    (hbr : ∀ ξ s, PRank (row τ) ξ.2 s → (Z ξ).H = b s) (m : ℤ) (x : ℤ) :
    (∀ n : ℕ, n < 4 ^ a - 2 → IsFree (phaseOffsets (row τ)) d m (rfree (phaseOffsets (row τ)) d m + n) →
      (Z (x, rfree (phaseOffsets (row τ)) d m + n)).H = true) ∧
    (Z (x, rfree (phaseOffsets (row τ)) d m + (4 ^ a - 2 : ℕ))).H = false ∧
    (Z (x, rfree (phaseOffsets (row τ)) d m + (4 ^ a - 2 : ℕ))).parent.1.a.1.b2 = true := by
  obtain ⟨-, hr0, hlt⟩ := initial_zero (row τ) ha had m
  refine ⟨fun n hn hfree => ?_, ?_, ?_⟩
  · obtain ⟨r, -, hr⟩ := exists_prank_le_of_inFrame (row τ)
      (⟨m, hfree.1.le, hfree.2.1.le⟩ : InFrame (phaseOffsets (row τ)) d _)
    have hr3 := hlt n r hn hfree hr
    rw [hbr (x, _) r hr]
    have := hb (show r ≤ 2 * a - 3 by omega)
    rw [h1] at this
    revert this
    cases b r <;> decide
  · rw [hbr (x, _) _ hr0, h0]
  · rw [chi2_eq hτ (x, _) hr0]
    simp
    omega

/-- **Lemma 4.2, `d ≤ a`, on a legal decorated chart** (every phase): with the cutoff
`b_{2a-3} = 1`, `b_{2a-1} = 0`, every free coordinate of a depth-`d` row frame (`1 ≤ d ≤ a`) where
`H_row = 0` has `χ₂ = 0`: the parity guard rejects every zero. -/
theorem input_read_small {Z : Plane → DQuarter} {τ : ℕ → Bool × Bool}
    (hτ : IsQPhase (fun ξ => (Z ξ).toQ) τ) {b : ℕ → Bool} (hb : Antitone b) {a d : ℕ}
    (ha : 2 ≤ a) (hda : d ≤ a) (h1 : b (2 * a - 3) = true)
    (hbr : ∀ ξ s, PRank (row τ) ξ.2 s → (Z ξ).H = b s) (m : ℤ) (x : ℤ) {n : ℕ}
    (hfree : IsFree (phaseOffsets (row τ)) d m (rfree (phaseOffsets (row τ)) d m + n))
    (hH : (Z (x, rfree (phaseOffsets (row τ)) d m + n)).H = false) :
    (Z (x, rfree (phaseOffsets (row τ)) d m + n)).parent.1.a.1.b2 = false := by
  obtain ⟨r, -, hr⟩ := exists_prank_le_of_inFrame (row τ)
    (⟨m, hfree.1.le, hfree.2.1.le⟩ : InFrame (phaseOffsets (row τ)) d _)
  have hbr' := hbr (x, _) r hr
  rw [hH] at hbr'
  have hra : 2 * a - 2 ≤ r := by
    by_contra hlt
    have := hb (show r ≤ 2 * a - 3 by omega)
    rw [h1, ← hbr'] at this
    exact absurd this (by decide)
  have hev := free_rank_even (row τ) ha hda m hfree hr hra
  rw [chi2_eq hτ (x, _) hr, decide_eq_false_iff_not]
  omega

end UND.Chart
