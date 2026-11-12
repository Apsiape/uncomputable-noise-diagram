/-
# The threshold `ε_*` (27), the search for `n₀` (28), and the final intervals (17)

Node Q3 of `BLUEPRINT.md` (Part A.9), with the interval clauses of Prop 9.2 (part of Q5).

* (25)–(26): `B = 4^k` (`Bparam`), `s = ⌈3CB/4⌉` (`sParam`), `λ = 176`, `M = 196608`,
  `N₀ = binom((2λ)⁴, M)` (`N0`), `Δ_rare = 10⁶[κ + B + (2λ)⁴ + q + T + 1]` with `κ` of Prop 2.1
  (`DeltaRareOf B`), `K_rare = 2²⁰(2Δ_rare²)^513` (`KrareOf B`, `Krare`);
* (27): `ε_* = min{C/100, (64K_mem)^{-4}, (64K_hist)^{-44}, [64K_rare(N₀+1)]^{-16}}`
  (`epsStarOf B N₀`, `epsStar`), a positive rational (`epsStar_pos`);
* (28): the least `n₀ ≥ k + 2` with `21C/(10(2·4^{n₀+1} - 1)) < ε_*` (`n0Param := Nat.find`);
  the search terminates because the left side tends to zero (`exists_n0Search`);
* the final intervals `I_n = (2C/ℓ_a, 21C/(10ℓ_a))`, `a = n + n₀` (`loF`, `hiF`), a window family
  (`isWindowFamily_final`);
* Prop 9.2: `I_n ⊂ (0, ε_*)` (`window_subset`), `ε ≤ C/100` on the windows, `a ≥ k + 3 ≥ 4`
  (`a_ge`), and the ruler margins (18) `ℓ_{a-1} < W`, `2W < ℓ_a` for `W = ⌊C/ε⌋`
  (`ruler_margins`, proved for every `c ≥ 1` and every `n₀`).

**Kernel discipline.** `kParam` and `n0Param` are `Nat.find`s, `B = 4^{52386}`, `N₀` is a binomial
coefficient with about `10⁶` digits and `K_rare` is larger still: the kernel must never try to
evaluate them. Lean's kernel unfolds abbreviation heads (`HMul.hMul`, …) first and then reduces
`Nat.mul`/`Nat.add` by evaluating their arguments, so even the `rfl` equation lemma of a definition
such as `Δ_rare := 10⁶ * (κ(B) + …)` with `B` closed exhausts memory. Hence every quantity is
defined as a function of its parameters (`DeltaRareOf B`, `KrareOf B`, `epsStarOf B N`), every
lemma is proved for variables, and the closed constants (`Krare := KrareOf Bparam`,
`epsStar := epsStarOf Bparam N0`) are only used through one-step instances, which the kernel checks
by a single delta step and syntactic equality.
-/
import UncomputableNoiseDiagram.Parameters.Search
import UncomputableNoiseDiagram.Windows
import Mathlib.Algebra.Order.Archimedean.Basic
import Mathlib.Algebra.Order.Floor.Semiring

set_option autoImplicit false

namespace UND.Param

open UND.Windows

/-! ## The constants (25)–(26) -/

/-- (25): `B = 4^k`. -/
@[irreducible] noncomputable def Bparam : ℕ := 4 ^ kParam

/-- Section 2: `s = ⌈3CB/4⌉`. -/
noncomputable def sParam : ℕ := ⌈3 * C * (Bparam : ℚ) / 4⌉₊

/-- (26): `N₀ = binom((2λ)⁴, M)`. -/
@[irreducible] noncomputable def N0 : ℕ := Nat.choose ((2 * lam) ^ 4) M

/-- (26): `Δ_rare = 10⁶[κ + B + (2λ)⁴ + q + T + 1]`, `κ = 2B(n_A + n_Q + 2)` (Prop 2.1), as a
function of `B`. -/
def DeltaRareOf (B : ℕ) : ℕ := 10 ^ 6 * (kappa B + B + (2 * lam) ^ 4 + q + T + 1)

/-- (26): `K_rare = 2²⁰ (2Δ_rare²)^513`, as a function of `B`. -/
def KrareOf (B : ℕ) : ℕ := 2 ^ 20 * (2 * DeltaRareOf B ^ 2) ^ 513

/-- (26): `K_rare` for the selected `B`. -/
noncomputable def Krare : ℕ := KrareOf Bparam

theorem DeltaRareOf_pos (B : ℕ) : 0 < DeltaRareOf B := by
  unfold DeltaRareOf
  positivity

theorem KrareOf_pos (B : ℕ) : 0 < KrareOf B := by
  have := DeltaRareOf_pos B
  unfold KrareOf
  positivity

theorem Krare_pos : 0 < Krare := KrareOf_pos Bparam

theorem C_pos : 0 < C := by
  unfold C
  have : (0 : ℚ) < cden := by exact_mod_cast cden_pos
  positivity

theorem C_eq_inv : C = (cden : ℚ)⁻¹ := one_div _

/-! ## The threshold (27) -/

/-- (27) as a function of `B` and `N₀`:
`min{C/100, (64K_mem)^{-4}, (64K_hist)^{-44}, [64K_rare(N₀+1)]^{-16}}`. -/
noncomputable def epsStarOf (B N : ℕ) : ℚ :=
  min (min (C / 100) ((((64 * Kmem : ℕ) : ℚ) ^ 4)⁻¹))
    (min ((((64 * Khist : ℕ) : ℚ) ^ 44)⁻¹) ((((64 * KrareOf B * (N + 1) : ℕ) : ℚ) ^ 16)⁻¹))

/-- (27): `ε_*` for the selected `B` and `N₀`. -/
noncomputable def epsStar : ℚ := epsStarOf Bparam N0

theorem epsStarOf_pos (B N : ℕ) : 0 < epsStarOf B N := by
  have h1 : (0 : ℚ) < ((64 * Kmem : ℕ) : ℚ) := Nat.cast_pos.2 (Nat.mul_pos (by norm_num) Kmem_pos)
  have h2 : (0 : ℚ) < ((64 * Khist : ℕ) : ℚ) :=
    Nat.cast_pos.2 (Nat.mul_pos (by norm_num) Khist_pos)
  have h3 : (0 : ℚ) < ((64 * KrareOf B * (N + 1) : ℕ) : ℚ) :=
    Nat.cast_pos.2 (Nat.mul_pos (Nat.mul_pos (by norm_num) (KrareOf_pos B)) (Nat.succ_pos N))
  have hC := C_pos
  unfold epsStarOf
  exact lt_min (lt_min (by positivity) (by positivity)) (lt_min (by positivity) (by positivity))

theorem epsStarOf_le_C (B N : ℕ) : epsStarOf B N ≤ C / 100 :=
  (min_le_left _ _).trans (min_le_left _ _)

theorem epsStarOf_le_mem (B N : ℕ) : epsStarOf B N ≤ (((64 * Kmem : ℕ) : ℚ) ^ 4)⁻¹ :=
  (min_le_left _ _).trans (min_le_right _ _)

theorem epsStarOf_le_hist (B N : ℕ) : epsStarOf B N ≤ (((64 * Khist : ℕ) : ℚ) ^ 44)⁻¹ :=
  (min_le_right _ _).trans (min_le_left _ _)

theorem epsStarOf_le_rare (B N : ℕ) :
    epsStarOf B N ≤ (((64 * KrareOf B * (N + 1) : ℕ) : ℚ) ^ 16)⁻¹ :=
  (min_le_right _ _).trans (min_le_right _ _)

theorem epsStar_pos : 0 < epsStar := epsStarOf_pos Bparam N0

theorem epsStar_le_C : epsStar ≤ C / 100 := epsStarOf_le_C Bparam N0

theorem epsStar_le_mem : epsStar ≤ (((64 * Kmem : ℕ) : ℚ) ^ 4)⁻¹ := epsStarOf_le_mem Bparam N0

theorem epsStar_le_hist : epsStar ≤ (((64 * Khist : ℕ) : ℚ) ^ 44)⁻¹ :=
  epsStarOf_le_hist Bparam N0

/-- `K_rare = K_rare(B)` (one delta step; never `unfold Krare`, whose proof term makes the kernel
evaluate). -/
theorem Krare_eq : Krare = KrareOf Bparam := rfl

theorem epsStar_le_rare : epsStar ≤ (((64 * Krare * (N0 + 1) : ℕ) : ℚ) ^ 16)⁻¹ := by
  rw [Krare_eq]
  exact epsStarOf_le_rare Bparam N0

/-! ## The search (28) -/

/-- (28): the conditions on `n₀`: `n₀ ≥ k + 2` and `21C/(10(2·4^{n₀+1} - 1)) < ε_*`. -/
def N0Search (n0 : ℕ) : Prop :=
  kParam + 2 ≤ n0 ∧ 21 * C / (10 * (2 * (4 : ℚ) ^ (n0 + 1) - 1)) < epsStar

/-- `ℓ_d = 2·4^d - 1` over `ℚ`. -/
theorem ell_cast (d : ℕ) : (ell d : ℚ) = 2 * (4 : ℚ) ^ d - 1 := by
  have h := ell_add_one d
  have : ((ell d + 1 : ℕ) : ℚ) = ((2 * 4 ^ d : ℕ) : ℚ) := by rw [h]
  push_cast at this
  linarith

/-- The left side of (28) tends to zero: for all `k`, `C > 0`, `e > 0` some `n₀ ≥ k + 2` passes. -/
theorem exists_n0_general (k : ℕ) (C e : ℚ) (_hC : 0 < C) (he : 0 < e) :
    ∃ n0, k + 2 ≤ n0 ∧ 21 * C / (10 * (2 * (4 : ℚ) ^ (n0 + 1) - 1)) < e := by
  obtain ⟨n1, hn1⟩ := pow_unbounded_of_one_lt (21 * C / (10 * e)) (by norm_num : (1 : ℚ) < 4)
  refine ⟨max n1 (k + 2), le_max_right _ _, ?_⟩
  have h4 : (4 : ℚ) ^ n1 ≤ (4 : ℚ) ^ (max n1 (k + 2) + 1) :=
    pow_le_pow_right₀ (by norm_num) (by omega)
  generalize max n1 (k + 2) = n at h4 ⊢
  have hden : (4 : ℚ) ^ (n + 1) ≤ 2 * (4 : ℚ) ^ (n + 1) - 1 := by
    have : (1 : ℚ) ≤ (4 : ℚ) ^ (n + 1) := one_le_pow₀ (by norm_num)
    linarith
  have hX : 21 * C / (10 * e) < (4 : ℚ) ^ (n + 1) := hn1.trans_le h4
  rw [div_lt_iff₀ (by positivity)] at hX
  have hpos : (0 : ℚ) < (4 : ℚ) ^ (n + 1) := by positivity
  have hdpos : (0 : ℚ) < 10 * (2 * (4 : ℚ) ^ (n + 1) - 1) := by linarith
  rw [div_lt_iff₀ hdpos]
  nlinarith

/-- The search (28) terminates (Prop 9.2: "its left side tends to zero"). -/
theorem exists_n0Search : ∃ n0, N0Search n0 :=
  exists_n0_general kParam C epsStar C_pos epsStar_pos

/-- (28): the least `n₀` passing the search, as printed (`Nat.find` with classical
decidability). -/
noncomputable def n0Param : ℕ := @Nat.find N0Search (Classical.decPred _) exists_n0Search

theorem n0Search_n0Param : N0Search n0Param :=
  @Nat.find_spec N0Search (Classical.decPred _) exists_n0Search

theorem n0Param_ge : kParam + 2 ≤ n0Param := n0Search_n0Param.1

/-! ## The final intervals (17) -/

/-- (17) with `C = 1/cden` and `n₀ = n0Param`: the lower endpoint `2C/ℓ_{n+n₀}`. -/
noncomputable def loF (n : ℕ) : ℚ := lo cden n0Param n

/-- (17): the upper endpoint `21C/(10ℓ_{n+n₀})`. -/
noncomputable def hiF (n : ℕ) : ℚ := hi cden n0Param n

/-- The final intervals form a computable disjoint window family (Theorem 9.3). -/
theorem isWindowFamily_final : IsWindowFamily loF hiF :=
  isWindowFamily_windows cden n0Param cden_pos

/-- For every `c ≥ 1`, `n₀` and `n ≥ 1`: if `n₀` passes (28) for the threshold `e` (with
`C = 1/c`), then `hi c n₀ n < e` (`ℓ_{n+n₀} ≥ ℓ_{n₀+1}`). -/
theorem hi_lt_of_search (c n0 n : ℕ) (hc : 1 ≤ c) (hn : 1 ≤ n) (e : ℚ)
    (h : 21 * (1 / (c : ℚ)) / (10 * (2 * (4 : ℚ) ^ (n0 + 1) - 1)) < e) : hi c n0 n < e := by
  have hcq : (0 : ℚ) < c := by exact_mod_cast hc
  have hmono : (ell (n0 + 1) : ℚ) ≤ (ell (n + n0) : ℚ) := by
    exact_mod_cast ell_mono (by omega)
  have hpos : (0 : ℚ) < (ell (n0 + 1) : ℚ) := by exact_mod_cast ell_pos _
  rw [← ell_cast] at h
  have e1 : hi c n0 n = 21 * (1 / (c : ℚ)) / (10 * (ell (n + n0) : ℚ)) := by
    unfold hi
    field_simp
  rw [e1]
  refine lt_of_le_of_lt ?_ h
  exact div_le_div_of_nonneg_left (by positivity) (by positivity) (by linarith)

/-- Prop 9.2: for `n ≥ 1`, `I_n` lies below `ε_*`. -/
theorem hiF_lt_epsStar {n : ℕ} (hn : 1 ≤ n) : hiF n < epsStar :=
  hi_lt_of_search cden n0Param n cden_pos hn epsStar n0Search_n0Param.2

/-- Prop 9.2: `I_n ⊂ (0, ε_*)` for every `n ≥ 1`. -/
theorem window_subset {n : ℕ} (hn : 1 ≤ n) :
    window loF hiF n ⊆ Set.Ioo (0 : ℝ) (epsStar : ℝ) := by
  intro ε hε
  have hfam := (isWindowFamily_final.2.2.1 n hn)
  have h1 : (0 : ℝ) < (loF n : ℝ) := by exact_mod_cast hfam.1
  have h2 : ((hiF n : ℚ) : ℝ) < (epsStar : ℝ) := by exact_mod_cast hiF_lt_epsStar hn
  exact ⟨h1.trans hε.1, hε.2.trans h2⟩

/-- Section 6: on the windows `ε ≤ C/100`. -/
theorem le_C_div_100 {n : ℕ} (hn : 1 ≤ n) {ε : ℝ} (hε : ε ∈ window loF hiF n) :
    ε ≤ (C : ℝ) / 100 := by
  have h := (window_subset hn hε).2
  have : ((epsStar : ℚ) : ℝ) ≤ ((C / 100 : ℚ) : ℝ) := by exact_mod_cast epsStar_le_C
  push_cast at this
  linarith

/-- Prop 9.2: `a = n + n₀ ≥ k + 3 ≥ 4` for `n ≥ 1`. -/
theorem a_ge {n : ℕ} (hn : 1 ≤ n) : kParam + 3 ≤ n + n0Param ∧ 4 ≤ n + n0Param := by
  have h1 := n0Param_ge
  have h2 : 1 ≤ kParam := bsearch_kParam.1
  generalize kParam = k at *
  generalize n0Param = n0 at *
  omega

/-! ## The ruler margins (18) -/

/-- (18), for every `C = 1/c` and `n₀`: with `a = d + 1 = n + n₀` and `W = ⌊C/ε⌋`, every
`ε ∈ I_n` gives `ℓ_{a-1} < W` and `2W < ℓ_a` (the paper's `ℓ_a ≥ 2W`). -/
theorem ruler_margins (c n0 n d : ℕ) (hc : 1 ≤ c) (hd : n + n0 = d + 1) {ε : ℝ}
    (hε : ε ∈ window (lo c n0) (hi c n0) n) :
    ell d < ⌊(c : ℝ)⁻¹ / ε⌋₊ ∧ 2 * ⌊(c : ℝ)⁻¹ / ε⌋₊ < ell (d + 1) := by
  obtain ⟨hlo, hhi⟩ := hε
  have hcpos : (0 : ℝ) < c := by exact_mod_cast hc
  have hl : (0 : ℝ) < (ell (d + 1) : ℝ) := by exact_mod_cast ell_pos _
  have hsucc : (ell (d + 1) : ℝ) = 4 * ell d + 3 := by exact_mod_cast ell_succ d
  have hlo' : 2 / ((c : ℝ) * ell (d + 1)) < ε := by
    have : ((lo c n0 n : ℚ) : ℝ) = 2 / ((c : ℝ) * ell (d + 1)) := by
      unfold lo; rw [hd]; push_cast; ring
    rwa [this] at hlo
  have hhi' : ε < 21 / (10 * (c : ℝ) * ell (d + 1)) := by
    have : ((hi c n0 n : ℚ) : ℝ) = 21 / (10 * (c : ℝ) * ell (d + 1)) := by
      unfold hi; rw [hd]; push_cast; ring
    rwa [this] at hhi
  have hεpos : 0 < ε := lt_trans (by positivity) hlo'
  -- `C/ε < ℓ_a / 2`
  have hup : (c : ℝ)⁻¹ / ε < (ell (d + 1) : ℝ) / 2 := by
    rw [div_lt_iff₀ hεpos]
    rw [div_lt_iff₀ (by positivity)] at hlo'
    have : (c : ℝ)⁻¹ * ((c : ℝ) * ell (d + 1)) = ell (d + 1) := by field_simp
    nlinarith [inv_pos.2 hcpos]
  -- `C/ε > 10 ℓ_a / 21 ≥ ℓ_{a-1} + 1`
  have hdown : (ell d : ℝ) + 1 < (c : ℝ)⁻¹ / ε := by
    rw [lt_div_iff₀ (by positivity)] at hhi'
    rw [hsucc] at hhi'
    have h0 : (0 : ℝ) ≤ ell d := Nat.cast_nonneg _
    have hce : 0 < (c : ℝ) * ε := by positivity
    have hk : 21 * ((c : ℝ) * ε * (ell d + 1)) ≤ (c : ℝ) * ε * (40 * ell d + 30) := by
      nlinarith
    have hlt : (c : ℝ) * ε * (ell d + 1) < 1 := by nlinarith
    have e : (c : ℝ)⁻¹ = 1 / c := (one_div _).symm
    rw [lt_div_iff₀ hεpos, e, lt_div_iff₀ hcpos]
    nlinarith
  constructor
  · have : ((ell d + 1 : ℕ) : ℝ) ≤ (c : ℝ)⁻¹ / ε := by push_cast; linarith
    have := Nat.le_floor this
    omega
  · have hfl : (⌊(c : ℝ)⁻¹ / ε⌋₊ : ℝ) ≤ (c : ℝ)⁻¹ / ε :=
      Nat.floor_le (by positivity)
    have : ((2 * ⌊(c : ℝ)⁻¹ / ε⌋₊ : ℕ) : ℝ) < (ell (d + 1) : ℝ) := by push_cast; linarith
    exact_mod_cast this

end UND.Param
