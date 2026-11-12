/-
# The fixed geometry and the exact integer constants (Sections 2, 5, 8 and 9)

Leaves of Part A.9 of `BLUEPRINT.md`: the numbers fixed in (1) and Sections 5, 8, 9 that do not
depend on the searches for `k` and `n₀`, with the printed identities and inequalities.

* (1): `m = 16`, `L = 160`, `K = 16⁴`, `q = 5K`, `h = 4K`; `2h > q` (the quorum letter is unique),
  `q - h = K`, `2h - q = 3K`; Section 2: `T = 500`; Section 8: `V = L + m - 1 = 175`,
  `λ = L + m = 176`, `M = h - K = 3K = 196608`.
* (11) and Lemma 5.1: the five potentials sum to zero; the good gains are at least `160` (charge
  zero) and `ϱ₊ = 85` (the others); every gain is at least `-ϱ₋ = -715`; `A₀ = 4000/85 < 48`.
* (13): `[5 - 4 - 5/16] K = 45056`.
* Lemma 8.4: `Ω = 2·5·4·175 = 7000`, `H₀ = A₀ + 7000/85 = 11000/85 < 130`, `2H₀ + 6 < 282 < 512`.
* Lemma 9.1: the role count `6(T + 7) ≤ 32(T + 2)`, the degree bound
  `2·32(T+2)·5(18q+10) ≤ 640(T+2)(9q+10) < Δ`, the rare-graph degree bound, and the counting sum
  `2 Σ_{e ≤ N} x^e ≤ 4 x^N` (`x ≥ 2`) with `4 (2Δ²)^{256g} ≤ K_mem^g`.
* Prop 2.1: `B(n_A + n_Q) + (B + 1) ≤ B(n_A + n_Q + 2)` for `B ≥ 1`.
-/
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.FinCases
import Mathlib.Data.Rat.Cast.Order

set_option autoImplicit false

namespace UND.Param

/-! ## (1) and Section 2 -/

/-- (1): the provider block side `m = 16`. -/
def m : ℕ := 16
/-- (1): the cluster spacing `L = 160`. -/
def L : ℕ := 160
/-- (1): the cluster size `K = 16⁴`. -/
def K : ℕ := 16 ^ 4
/-- (1): the number of checked providers `q = 5K`. -/
def q : ℕ := 5 * K
/-- (1): the quorum `h = 4K`. -/
def h : ℕ := 4 * K
/-- Section 2.2: the forecast depth `T = 500`. -/
def T : ℕ := 500
/-- Section 8.2: `V = L + m - 1`. -/
def V : ℕ := L + m - 1
/-- Section 8.3: `λ = L + m`. -/
def lam : ℕ := L + m
/-- Section 8.3: `M = h - K`. -/
def M : ℕ := h - K

theorem K_eq : K = 65536 := by norm_num [K]
theorem q_eq : q = 327680 := by norm_num [q, K]
theorem h_eq : h = 262144 := by norm_num [h, K]
/-- Section 2.1: "Since `2h > q`, that letter is unique." -/
theorem q_lt_two_h : q < 2 * h := by norm_num [q, h, K]
/-- Lemma 5.3: a live output has at most `K = q - h` failed checked providers. -/
theorem q_sub_h : q - h = K := by norm_num [q, h, K]
/-- Lemma 5.3: two checked-provider sets of size `h` overlap in at least `2h - q = 3K`. -/
theorem two_h_sub_q : 2 * h - q = 3 * K := by norm_num [q, h, K]
theorem V_eq : V = 175 := by norm_num [V, L, m]
theorem lam_eq : lam = 176 := by norm_num [lam, L, m]
/-- Section 8.3: `M = h - K = 3K = 196608`. -/
theorem M_eq : M = 3 * K ∧ M = 196608 := by norm_num [M, h, K]
/-- Section 7: a bad forecast has at least `q - h + 1 = K + 1` failed providers. -/
theorem q_sub_h_add_one : q - h + 1 = K + 1 := by rw [q_sub_h]

/-! ## (11): the five potentials of Section 5 -/

/-- Section 5.1: `ψ₀(P, t) = 5 Σ_i P_i + 640 t` (provider coordinates `P ∈ ℤ⁴`). -/
def psi0 (P : Fin 4 → ℤ) (t : ℤ) : ℤ := 5 * (∑ i, P i) + 640 * t
/-- Section 5.1: `ψ_i(P, t) = -5 P_i - 160 t` (`1 ≤ i ≤ 4`, here `i : Fin 4`). -/
def psiI (i : Fin 4) (P : Fin 4 → ℤ) (t : ℤ) : ℤ := -5 * P i - 160 * t

/-- Section 5.1: "Their sum is zero." -/
theorem psi_sum (P : Fin 4 → ℤ) (t : ℤ) : psi0 P t + ∑ i, psiI i P t = 0 := by
  simp only [psi0, psiI, Fin.sum_univ_four]
  ring

/-- The cluster offsets `C₀ = 0`, `C_i = L e_i`: cluster `none` is `S₀`, cluster `some i` is
`S_{i+1}`; a provider vector of cluster `c` is `C_c + o`, `o ∈ {0, …, 15}⁴`. -/
def clusterOffset (c : Option (Fin 4)) : Fin 4 → ℤ :=
  match c with
  | none => 0
  | some i => fun j => if j = i then 160 else 0

/-- A block offset `o ∈ {0, …, m - 1}⁴ = {0, …, 15}⁴`. -/
def IsBlockOffset (o : Fin 4 → ℤ) : Prop := ∀ j, 0 ≤ o j ∧ o j ≤ 15

/-- (11), charge zero: on `P ↦ P + s`, `t ↦ t - 1` with `s` in a nonzero cluster the gain of `ψ₀`
is at least `160`. -/
theorem gain_zero_good (P : Fin 4 → ℤ) (t : ℤ) (i : Fin 4) (o : Fin 4 → ℤ)
    (ho : IsBlockOffset o) :
    psi0 P t + 160 ≤ psi0 (P + (clusterOffset (some i) + o)) (t - 1) := by
  simp only [psi0, Pi.add_apply, clusterOffset, Finset.sum_add_distrib, Fin.sum_univ_four]
  have h0 := (ho 0).1; have h1 := (ho 1).1; have h2 := (ho 2).1; have h3 := (ho 3).1
  fin_cases i <;> simp <;> linarith

/-- (11), charge `i ≥ 1`: with `s` in a cluster other than `i` the gain of `ψ_i` is at least
`ϱ₊ = 160 - 5·15 = 85`. -/
theorem gain_i_good (P : Fin 4 → ℤ) (t : ℤ) (i : Fin 4) (c : Option (Fin 4))
    (hc : c ≠ some i) (o : Fin 4 → ℤ) (ho : IsBlockOffset o) :
    psiI i P t + 85 ≤ psiI i (P + (clusterOffset c + o)) (t - 1) := by
  simp only [psiI, Pi.add_apply]
  have hcl : clusterOffset c i = 0 := by
    cases c with
    | none => rfl
    | some j =>
      have hji : i ≠ j := fun e => hc (by rw [e])
      simp [clusterOffset, hji]
  rw [hcl]
  have := (ho i).2
  linarith

/-- (11): every gain of `ψ₀` is at least `-ϱ₋ = -(4·160 + 5·15) = -715`. -/
theorem gain_zero_worst (P : Fin 4 → ℤ) (t : ℤ) (c : Option (Fin 4)) (o : Fin 4 → ℤ)
    (ho : IsBlockOffset o) :
    psi0 P t - 715 ≤ psi0 (P + (clusterOffset c + o)) (t - 1) := by
  simp only [psi0, Pi.add_apply, Finset.sum_add_distrib, Fin.sum_univ_four]
  have h0 := (ho 0).1; have h1 := (ho 1).1; have h2 := (ho 2).1; have h3 := (ho 3).1
  cases c with
  | none => simp [clusterOffset]; linarith
  | some i => fin_cases i <;> simp [clusterOffset] <;> linarith

/-- (11): every gain of `ψ_i` is at least `-715`. -/
theorem gain_i_worst (P : Fin 4 → ℤ) (t : ℤ) (i : Fin 4) (c : Option (Fin 4)) (o : Fin 4 → ℤ)
    (ho : IsBlockOffset o) :
    psiI i P t - 715 ≤ psiI i (P + (clusterOffset c + o)) (t - 1) := by
  simp only [psiI, Pi.add_apply]
  have hcl : clusterOffset c i ≤ 160 := by
    cases c with
    | none => simp [clusterOffset]
    | some j => simp only [clusterOffset]; split_ifs <;> norm_num
  have := (ho i).2
  linarith

/-- (11): `ϱ₊ = 160 - 5·15 = 85` and `ϱ₋ = 4·160 + 5·15 = 715`. -/
theorem rho_values : (160 : ℤ) - 5 * 15 = 85 ∧ (4 : ℤ) * 160 + 5 * 15 = 715 := by norm_num

/-- Section 5.1: `A₀ = 5(1 + ϱ₋/ϱ₊) = 4000/85 < 48`. -/
theorem A0_eq : (5 : ℚ) * (1 + 715 / 85) = 4000 / 85 ∧ (4000 : ℚ) / 85 < 48 := by norm_num

/-- (13): `[5 - 4 - 5/16] K = 45056 > 0`. -/
theorem spancount : ((5 : ℚ) - 4 - 5 / 16) * K = 45056 := by
  norm_num [K]

/-- Lemma 5.3: the injective pairs per coordinate step, `5K(1 - 1/16)`, minus the four discards
of `K` each (failed supports and marked-parent offsets for both roots), leave (13). -/
theorem spancount' : (5 : ℚ) * K * (1 - 1 / 16) - 4 * K = 45056 := by
  norm_num [K]

/-! ## Section 8 constants -/

/-- Lemma 8.4: `Ω = 2·5·4·175 = 7000`. -/
theorem Omega_eq : 2 * 5 * 4 * V = 7000 := by norm_num [V, L, m]

/-- Lemma 8.4: `H₀ = A₀ + 7000/85 = 11000/85 < 130`. -/
theorem H0_eq : (4000 : ℚ) / 85 + 7000 / 85 = 11000 / 85 ∧ (11000 : ℚ) / 85 < 130 := by norm_num

/-- Lemma 8.4 and Lemma 9.1: `(2H₀ + 6) g < 282 g < 512 g` (`g ≥ 1`), and the memory count
`149 g < 256 g`. -/
theorem rare_edges (g : ℕ) (hg : 1 ≤ g) :
    (2 * (11000 / 85 : ℚ) + 6) * g < 282 * g ∧ (282 : ℚ) * g < 512 * g ∧
      (149 : ℚ) * g < 256 * g := by
  have : (1 : ℚ) ≤ g := by exact_mod_cast hg
  refine ⟨?_, ?_, ?_⟩ <;> nlinarith

/-! ## Lemma 9.1: degrees and the counting sum -/

/-- (24): `Δ = 10⁶ (T + 2)(9q + 10)`. -/
def Delta : ℕ := 10 ^ 6 * (T + 2) * (9 * q + 10)

/-- (24): `K_mem = 2²⁰ (2Δ²)^257`. -/
def Kmem : ℕ := 2 ^ 20 * (2 * Delta ^ 2) ^ 257

/-- (24): `K_hist = 2⁴⁰ [100(V + 1)]^10 (2Δ²)^100`. -/
def Khist : ℕ := 2 ^ 40 * (100 * (V + 1)) ^ 10 * (2 * Delta ^ 2) ^ 100

theorem Delta_eq : Delta = 1480463260000000 := by decide

/-- Lemma 9.1: the roles of the projected memory graph: `6(T + 7) ≤ 32(T + 2)`. -/
theorem roles_le : 6 * (T + 7) ≤ 32 * (T + 2) := by norm_num [T]

/-- Lemma 9.1: the undirected degree `2·32(T+2)·5(18q+10) ≤ 640(T+2)(9q+10) < Δ`. -/
theorem degree_le : 2 * 32 * (T + 2) * (5 * (18 * q + 10)) ≤ 640 * (T + 2) * (9 * q + 10) ∧
    640 * (T + 2) * (9 * q + 10) < Delta := by
  decide

/-- Lemma 9.1, rare groups: `64[2κ + 2B + 2(2λ)⁴ + 18q + 2(T+1)] < Δ_rare` for all `κ, B`, with
`Δ_rare = 10⁶[κ + B + (2λ)⁴ + q + T + 1]` (26). -/
theorem rare_degree_lt (κ B : ℕ) :
    64 * (2 * κ + 2 * B + 2 * (2 * lam) ^ 4 + 18 * q + 2 * (T + 1)) <
      10 ^ 6 * (κ + B + (2 * lam) ^ 4 + q + T + 1) := by
  norm_num [lam, L, m, q, K, T]
  omega

/-- Lemma 9.1: `2 Σ_{e=0}^{N} x^e ≤ 4 x^N` for `x ≥ 2`. -/
theorem two_geom_le (x N : ℕ) (hx : 2 ≤ x) :
    2 * ∑ e ∈ Finset.range (N + 1), x ^ e ≤ 4 * x ^ N := by
  induction N with
  | zero => simp
  | succ N ih =>
    rw [Finset.sum_range_succ, mul_add, pow_succ]
    have hxN : 0 ≤ x ^ N := Nat.zero_le _
    nlinarith

/-- Lemma 9.1: `4 (2Δ²)^{256 g} ≤ K_mem^g` for `g ≥ 1`. -/
theorem four_le_Kmem_pow (g : ℕ) (hg : 1 ≤ g) :
    4 * (2 * Delta ^ 2) ^ (256 * g) ≤ Kmem ^ g := by
  obtain ⟨g, rfl⟩ : ∃ g', g = g' + 1 := ⟨g - 1, by omega⟩
  have key : ∀ X : ℕ, 1 ≤ X → 4 * X ^ (256 * (g + 1)) ≤ (2 ^ 20 * X ^ 257) ^ (g + 1) := by
    intro X hX1
    rw [mul_pow, ← pow_mul X]
    have h1 : 4 ≤ (2 ^ 20) ^ (g + 1) := by
      calc 4 ≤ 2 ^ 20 := by norm_num
        _ ≤ (2 ^ 20) ^ (g + 1) := Nat.le_self_pow (by omega) _
    have h2 : X ^ (256 * (g + 1)) ≤ X ^ (257 * (g + 1)) := Nat.pow_le_pow_right hX1 (by omega)
    exact Nat.mul_le_mul h1 h2
  have hD : 0 < Delta := by rw [Delta_eq]; norm_num
  unfold Kmem
  exact key (2 * Delta ^ 2) (Nat.mul_pos (by norm_num) (pow_pos hD 2))

/-! ## Proposition 2.1 -/

/-- Prop 2.1: `n_A = 9q`. -/
def nA : ℕ := 9 * q
/-- Prop 2.1: `n_Q = (2T + 1)² [T(L + m - 1) + 1]⁴`. -/
def nQ : ℕ := (2 * T + 1) ^ 2 * (T * (L + m - 1) + 1) ^ 4
/-- Prop 2.1: `κ = 2B(n_A + n_Q + 2)`. -/
def kappa (B : ℕ) : ℕ := 2 * B * (nA + nQ + 2)

/-- Proof of Prop 2.1: `B(n_A + n_Q) + (B + 1) ≤ B(n_A + n_Q + 2)` for `B ≥ 1`, and the two
dependency directions together give `κ`. -/
theorem parents_le (B : ℕ) (hB : 1 ≤ B) :
    B * (nA + nQ) + (B + 1) ≤ B * (nA + nQ + 2) ∧
      2 * (B * (nA + nQ + 2)) = kappa B := by
  constructor
  · nlinarith
  · simp only [kappa]; ring

end UND.Param
