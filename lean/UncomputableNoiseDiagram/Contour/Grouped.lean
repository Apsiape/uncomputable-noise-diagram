/-
# Lemma 5.1 (grouped terminal estimate), abstract form

Node C1 of `BLUEPRINT.md` (Part A.5). ADAPTED from the forgetting core's contour lemma
(`FixedNoiseErgodicity/Combinatorics/Contour.lean`, same authors: support systems, greedy arms,
poles, fronts, the splitting invariant, `exists_poles`, `exists_bij`, the potential count),
generalized as Lemma 5.1 requires:

* **groups**: terminal leaves carry group names (`grp`); the descendant sets `Φ(θ)` are sets of
  group names (`Term θ γ`), and the splitting invariant pairs poles with groups;
* **unary links**: a vertex may have one successor with zero potential change for every charge
  (`UN`, `un`); a unary exposure "cannot split a component" (`rel_frontU`);
* **inequality potentials**: a good edge raises `ψ_c` by at least `ϱ₊`, every edge lowers it by at
  most `ϱ₋` (the forgetting core has the exact increments `+1`, `1 - q`); the good support of each
  charge is one of the two selected supports (`good`);
* **group oscillations**: the five charge endpoints in one group are compared to a reference leaf
  (`hosc`), giving the terminal sum `≤ gΩ`;
* acyclicity is a rank strictly decreasing along every edge (`rk`), not a time decreasing by one.

Printed statement (Lemma 5.1). In a finite root-reachable acyclic support graph, let every
nonterminal have two selected supports and a good support for each of the five charges. Partition
its terminal leaves into groups. Suppose the sum of the five potential oscillations within any
group is at most `Ω`. One can select `g` distinct groups and a connected copied-arm witness
containing the root with `e ≤ A₀(g - 1) + Ωg/ϱ₊` positive support edges, counted with
multiplicity. Unary zero-potential links are permitted; they create no additional charge sources.
With singleton groups a nonterminal root has at least two terminal flags. If support edges
decrease time by one and group identifications preserve time, the span is at most `e`.

**Fidelity deviation (repaired statement; QB, session 2; to be corrected in v1.1.0).** The last
printed sentence is false when the permitted unary zero-potential links change time: the link
`(P, t) ↦ (P + D·(32,32,32,32), t - D)` changes every potential by `0` yet moves time by `D`, so
with singleton groups the edge count stays bounded while the span grows. Formalized here is the
repaired lemma: the edge bound (12) for arbitrary zero-potential unary links
(`grouped_terminal_estimate`), and the span bound only when unary links also preserve time
(`witness_span`, hypothesis `hun`). The two-terminal assertion needs a positive support edge in
the root witness: the root is binary (`S.NF ρ`), so each of its arms starts with one.

Main results:
* `exists_bij`: poles whose arms, for each charge, end in each group of `Φ(ρ)` exactly once;
* **`grouped_terminal_estimate`**: a set `P` of `g = |P|` poles (sources) containing the root pole,
  linked to it through shared groups, whose `c`-arms end in `g` distinct groups (the same `g`
  groups for every charge), with
  `ϱ₊ e ≤ (ϱ₊ + ϱ₋)·|C|·(g - 1) + Ω g` for `e` the number of binary (positive support) edges of
  the arms counted with multiplicity; with `|C| = 5`, `ϱ₊ = 85`, `ϱ₋ = 715` this is
  `e ≤ A₀(g - 1) + Ωg/ϱ₊`, `A₀ = 4000/85` (`UND.Param.A0_eq`);
* `grouped_terminal_estimate_paper`: the same with `|C| = 5`, `ϱ₊ = 85`, `ϱ₋ = 715`, in the printed
  form (12) `e ≤ A₀(g - 1) + Ωg/ϱ₊`;
* `witness_connected`: the copied-arm witness (arm edges and identification links between arm ends
  in one group, `witness`) is connected at the root;
* `singleton_two_le`: with singleton groups (`hosc_singleton`: then `Ω = 0`), `g ≥ 2`;
* `witness_span`: if support edges decrease time by one, unary links and group identifications
  preserve it, every witness vertex has time in `[time ρ - e, time ρ]` (the repaired span
  assertion; every application in the paper has such clocks: raw and deep-query contours, and the
  same-time groups of rare-birth contours; the memory count uses the edge bound only).
-/
import Mathlib.Logic.Relation
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Tactic.Linarith
import Mathlib.Data.Int.Interval
import Mathlib.Tactic.Ring
import FixedNoiseErgodicity.Combinatorics.EdgeCount

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UND.Contour

open Relation

/-- Lemma 5.1: a grouped support graph. Binary nonterminals (`NF`) have two selected supports
(`sup θ true`, `sup θ false`) and, for each charge `c`, a good one among them (`sup θ (good c θ)`);
unary vertices (`UN`) have one link `un θ`; the other vertices are terminal leaves, each with a
group name (`grp`). A rank strictly decreasing along every edge makes the graph acyclic. -/
structure GroupedSystem (V C Γ : Type*) where
  /-- a rank strictly decreasing along every edge (acyclicity) -/
  rk : V → ℕ
  /-- binary nonterminal vertices -/
  NF : V → Prop
  /-- unary vertices (zero-potential links) -/
  UN : V → Prop
  not_UN_of_NF : ∀ θ, NF θ → ¬ UN θ
  /-- the two selected supports of a binary vertex -/
  sup : V → Bool → V
  /-- the link of a unary vertex -/
  un : V → V
  /-- the good selected support of each charge -/
  good : C → V → Bool
  /-- the group name of a terminal leaf -/
  grp : V → Γ
  rk_sup : ∀ θ b, NF θ → rk (sup θ b) < rk θ
  rk_un : ∀ θ, UN θ → rk (un θ) < rk θ

namespace GroupedSystem

variable {V C Γ : Type*} (S : GroupedSystem V C Γ)

/-! ## Reachability and descendant groups -/

/-- A terminal leaf: neither binary nor unary. -/
def IsTerm (θ : V) : Prop := ¬ S.NF θ ∧ ¬ S.UN θ

/-- One edge of the graph: to a selected support, or along a unary link. -/
def Step (a b : V) : Prop := (S.NF a ∧ ∃ bb, b = S.sup a bb) ∨ (S.UN a ∧ b = S.un a)

/-- `b` is reached from `a` along edges. -/
def Reach (a b : V) : Prop := ReflTransGen S.Step a b

/-- `γ ∈ Φ(θ)`: a terminal leaf of group `γ` is reached from `θ` (the descendant group names). -/
def Term (θ : V) (γ : Γ) : Prop := ∃ φ, S.Reach θ φ ∧ S.IsTerm φ ∧ S.grp φ = γ

theorem not_NF_of_UN {θ : V} (h : S.UN θ) : ¬ S.NF θ := fun h' => S.not_UN_of_NF θ h' h

/-- Induction along edges (the rank decreases). -/
theorem rk_induction {P : V → Prop}
    (h : ∀ θ, (S.NF θ → ∀ b, P (S.sup θ b)) → (S.UN θ → P (S.un θ)) → P θ) (θ : V) : P θ := by
  suffices ∀ n θ, S.rk θ = n → P θ from this _ θ rfl
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro θ hθ
    exact h θ (fun hnf b => ih _ (by have := S.rk_sup θ b hnf; omega) _ rfl)
      (fun hu => ih _ (by have := S.rk_un θ hu; omega) _ rfl)

theorem eq_of_reach_of_isTerm {a b : V} (ha : S.IsTerm a) (h : S.Reach a b) : b = a := by
  rcases ReflTransGen.cases_head h with h | ⟨c, hac, _⟩
  · exact h.symm
  · rcases hac with ⟨hn, _⟩ | ⟨hu, _⟩
    · exact absurd hn ha.1
    · exact absurd hu ha.2

theorem reach_sup {θ : V} (h : S.NF θ) (b : Bool) : S.Reach θ (S.sup θ b) :=
  ReflTransGen.single (Or.inl ⟨h, b, rfl⟩)

theorem reach_un {θ : V} (h : S.UN θ) : S.Reach θ (S.un θ) :=
  ReflTransGen.single (Or.inr ⟨h, rfl⟩)

theorem term_trans {a θ : V} {γ : Γ} (h : S.Reach a θ) (h' : S.Term θ γ) : S.Term a γ := by
  obtain ⟨φ, h1, h2, h3⟩ := h'
  exact ⟨φ, h.trans h1, h2, h3⟩

theorem term_of_isTerm {θ : V} (h : S.IsTerm θ) : S.Term θ (S.grp θ) :=
  ⟨θ, ReflTransGen.refl, h, rfl⟩

theorem term_isTerm_iff {θ : V} {γ : Γ} (h : S.IsTerm θ) : S.Term θ γ ↔ S.grp θ = γ := by
  constructor
  · rintro ⟨φ, h1, -, rfl⟩
    rw [S.eq_of_reach_of_isTerm h h1]
  · rintro rfl
    exact S.term_of_isTerm h

theorem term_of_sup {θ : V} {γ : Γ} (h : S.NF θ) {b : Bool} (h' : S.Term (S.sup θ b) γ) :
    S.Term θ γ :=
  S.term_trans (S.reach_sup h b) h'

/-- `Φ(θ) = Φ(θ⁽¹⁾) ∪ Φ(θ⁽²⁾)` at a binary vertex. -/
theorem term_sup_iff {θ : V} {γ : Γ} (h : S.NF θ) :
    S.Term θ γ ↔ S.Term (S.sup θ true) γ ∨ S.Term (S.sup θ false) γ := by
  constructor
  · rintro ⟨φ, hr, ht, hg⟩
    rcases ReflTransGen.cases_head hr with rfl | ⟨c, hc, hcφ⟩
    · exact absurd h ht.1
    · rcases hc with ⟨-, bb, rfl⟩ | ⟨hu, -⟩
      · cases bb
        · exact Or.inr ⟨φ, hcφ, ht, hg⟩
        · exact Or.inl ⟨φ, hcφ, ht, hg⟩
      · exact absurd hu (S.not_UN_of_NF θ h)
  · rintro (h' | h')
    · exact S.term_of_sup h h'
    · exact S.term_of_sup h h'

/-- `Φ(θ) = Φ(un θ)` at a unary vertex. -/
theorem term_un_iff {θ : V} {γ : Γ} (h : S.UN θ) : S.Term θ γ ↔ S.Term (S.un θ) γ := by
  constructor
  · rintro ⟨φ, hr, ht, hg⟩
    rcases ReflTransGen.cases_head hr with rfl | ⟨c, hc, hcφ⟩
    · exact absurd h ht.2
    · rcases hc with ⟨hn, -⟩ | ⟨-, rfl⟩
      · exact absurd h (S.not_UN_of_NF _ hn)
      · exact ⟨φ, hcφ, ht, hg⟩
  · intro h'
    exact S.term_trans (S.reach_un h) h'

/-! ## Greedy arms -/

open Classical in
/-- The greedy successor for charge `c`: the good support at a binary vertex, the link at a unary
one. -/
def g (c : C) (θ : V) : V := if S.NF θ then S.sup θ (S.good c θ) else S.un θ

theorem g_of_NF {c : C} {θ : V} (h : S.NF θ) : S.g c θ = S.sup θ (S.good c θ) := by
  classical
  simp [g, h]

theorem g_of_UN {c : C} {θ : V} (h : S.UN θ) : S.g c θ = S.un θ := by
  classical
  simp [g, S.not_NF_of_UN h]

theorem rk_g {c : C} {θ : V} (h : S.NF θ ∨ S.UN θ) : S.rk (S.g c θ) < S.rk θ := by
  rcases h with h | h
  · rw [S.g_of_NF h]
    exact S.rk_sup θ _ h
  · rw [S.g_of_UN h]
    exact S.rk_un θ h

theorem reach_g {c : C} {θ : V} (h : S.NF θ ∨ S.UN θ) : S.Reach θ (S.g c θ) := by
  rcases h with h | h
  · rw [S.g_of_NF h]
    exact S.reach_sup h _
  · rw [S.g_of_UN h]
    exact S.reach_un h

open Classical in
/-- The end of the greedy `c`-arm from `θ`: follow `g_c` to a terminal leaf. -/
def gEnd (c : C) (θ : V) : V :=
  if _h : S.NF θ ∨ S.UN θ then gEnd c (S.g c θ) else θ
termination_by S.rk θ
decreasing_by exact S.rk_g _h

open Classical in
/-- The number of binary (positive support) edges of the greedy `c`-arm from `θ`. -/
def gBin (c : C) (θ : V) : ℕ :=
  if _h : S.NF θ ∨ S.UN θ then gBin c (S.g c θ) + (if S.NF θ then 1 else 0) else 0
termination_by S.rk θ
decreasing_by exact S.rk_g _h

open Classical in
/-- The number of edges (binary and unary) of the greedy `c`-arm from `θ`. -/
def gLen (c : C) (θ : V) : ℕ :=
  if _h : S.NF θ ∨ S.UN θ then gLen c (S.g c θ) + 1 else 0
termination_by S.rk θ
decreasing_by exact S.rk_g _h

theorem gEnd_of_step (c : C) {θ : V} (h : S.NF θ ∨ S.UN θ) :
    S.gEnd c θ = S.gEnd c (S.g c θ) := by
  rw [gEnd, dite_eq_left h]

theorem gEnd_of_isTerm (c : C) {θ : V} (h : S.IsTerm θ) : S.gEnd c θ = θ := by
  rw [gEnd, dite_eq_right (by rintro (h' | h') <;> [exact h.1 h'; exact h.2 h'])]

theorem gBin_of_NF (c : C) {θ : V} (h : S.NF θ) : S.gBin c θ = S.gBin c (S.g c θ) + 1 := by
  classical
  rw [gBin, dite_eq_left (Or.inl h)]
  simp [h]

theorem gBin_of_UN (c : C) {θ : V} (h : S.UN θ) : S.gBin c θ = S.gBin c (S.g c θ) := by
  classical
  rw [gBin, dite_eq_left (Or.inr h)]
  simp [S.not_NF_of_UN h]

theorem gBin_of_isTerm (c : C) {θ : V} (h : S.IsTerm θ) : S.gBin c θ = 0 := by
  rw [gBin, dite_eq_right (by rintro (h' | h') <;> [exact h.1 h'; exact h.2 h'])]

theorem gLen_of_step (c : C) {θ : V} (h : S.NF θ ∨ S.UN θ) :
    S.gLen c θ = S.gLen c (S.g c θ) + 1 := by
  rw [gLen, dite_eq_left h]

theorem gLen_of_isTerm (c : C) {θ : V} (h : S.IsTerm θ) : S.gLen c θ = 0 := by
  rw [gLen, dite_eq_right (by rintro (h' | h') <;> [exact h.1 h'; exact h.2 h'])]

theorem isTerm_of_not {θ : V} (h : ¬ (S.NF θ ∨ S.UN θ)) : S.IsTerm θ :=
  ⟨fun h' => h (Or.inl h'), fun h' => h (Or.inr h')⟩

/-- Induction along greedy steps. -/
theorem g_induction (c : C) {P : V → Prop} (hstep : ∀ θ, (S.NF θ ∨ S.UN θ) → P (S.g c θ) → P θ)
    (hterm : ∀ θ, S.IsTerm θ → P θ) (θ : V) : P θ := by
  refine S.rk_induction (fun θ ih1 ih2 => ?_) θ
  by_cases h : S.NF θ ∨ S.UN θ
  · refine hstep θ h ?_
    rcases h with h' | h'
    · rw [S.g_of_NF h']
      exact ih1 h' _
    · rw [S.g_of_UN h']
      exact ih2 h'
  · exact hterm θ (S.isTerm_of_not h)

theorem gEnd_isTerm (c : C) (θ : V) : S.IsTerm (S.gEnd c θ) := by
  refine S.g_induction c (P := fun θ => S.IsTerm (S.gEnd c θ)) (fun θ h ih => ?_)
    (fun θ h => ?_) θ
  · rw [S.gEnd_of_step c h]
    exact ih
  · rw [S.gEnd_of_isTerm c h]
    exact h

theorem reach_gEnd (c : C) (θ : V) : S.Reach θ (S.gEnd c θ) := by
  refine S.g_induction c (P := fun θ => S.Reach θ (S.gEnd c θ)) (fun θ h ih => ?_)
    (fun θ h => ?_) θ
  · rw [S.gEnd_of_step c h]
    exact (S.reach_g h).trans ih
  · rw [S.gEnd_of_isTerm c h]
    exact ReflTransGen.refl

theorem gEnd_term (c : C) (θ : V) : S.Term θ (S.grp (S.gEnd c θ)) :=
  ⟨_, S.reach_gEnd c θ, S.gEnd_isTerm c θ, rfl⟩

/-- Every descendant set is nonempty. -/
theorem exists_term (c : C) (θ : V) : ∃ γ, S.Term θ γ := ⟨_, S.gEnd_term c θ⟩

/-! ## Potentials -/

/-- Lemma 5.1, the potentials: they sum to zero at every vertex; a good edge raises `ψ_c` by at
least `ϱ₊`; every support edge lowers it by at most `ϱ₋`; unary links leave every `ψ_c`
unchanged. -/
def IsPotential [Fintype C] (ψ : C → V → ℤ) (ϱp ϱm : ℤ) : Prop :=
  (∀ θ, ∑ c, ψ c θ = 0) ∧
    (∀ θ c, S.NF θ → ψ c θ + ϱp ≤ ψ c (S.sup θ (S.good c θ))) ∧
    (∀ θ b c, S.NF θ → ψ c θ - ϱm ≤ ψ c (S.sup θ b)) ∧
    (∀ θ c, S.UN θ → ψ c (S.un θ) = ψ c θ)

/-- Along a greedy `c`-arm every binary edge is good for `c`. -/
theorem gEnd_psi [Fintype C] {ψ : C → V → ℤ} {ϱp ϱm : ℤ} (hψ : S.IsPotential ψ ϱp ϱm) (c : C)
    (θ : V) : ψ c θ + ϱp * S.gBin c θ ≤ ψ c (S.gEnd c θ) := by
  refine S.g_induction c (P := fun θ => ψ c θ + ϱp * S.gBin c θ ≤ ψ c (S.gEnd c θ))
    (fun θ h ih => ?_) (fun θ h => ?_) θ
  · rw [S.gEnd_of_step c h]
    rcases h with h | h
    · rw [S.gBin_of_NF c h]
      have h1 := hψ.2.1 θ c h
      rw [← S.g_of_NF h] at h1
      push_cast
      linarith
    · rw [S.gBin_of_UN c h]
      have h1 := hψ.2.2.2 θ c h
      rw [← S.g_of_UN (c := c) h] at h1
      linarith
  · rw [S.gEnd_of_isTerm c h, S.gBin_of_isTerm c h]
    simp

/-! ## Arm edges -/

section Edges

variable [DecidableEq V]

open Classical in
/-- The edges of the greedy `c`-arm from `θ`. -/
def gEdges (c : C) (θ : V) : Finset (Sym2 V) :=
  if _h : S.NF θ ∨ S.UN θ then insert s(θ, S.g c θ) (gEdges c (S.g c θ)) else ∅
termination_by S.rk θ
decreasing_by exact S.rk_g _h

theorem gEdges_of_step (c : C) {θ : V} (h : S.NF θ ∨ S.UN θ) :
    S.gEdges c θ = insert s(θ, S.g c θ) (S.gEdges c (S.g c θ)) := by
  rw [gEdges, dite_eq_left h]

theorem gEdges_of_isTerm (c : C) {θ : V} (h : S.IsTerm θ) : S.gEdges c θ = ∅ := by
  rw [gEdges, dite_eq_right (by rintro (h' | h') <;> [exact h.1 h'; exact h.2 h'])]

theorem gEdges_card_le (c : C) (θ : V) : (S.gEdges c θ).card ≤ S.gLen c θ := by
  refine S.g_induction c (P := fun θ => (S.gEdges c θ).card ≤ S.gLen c θ)
    (fun θ h ih => ?_) (fun θ h => ?_) θ
  · rw [S.gEdges_of_step c h, S.gLen_of_step c h]
    exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ih 1)
  · rw [S.gEdges_of_isTerm c h]
    simp

/-- Every arm edge leaves a reached nonterminal vertex along one of its edges. -/
theorem gEdges_spec (c : C) (θ : V) :
    ∀ e ∈ S.gEdges c θ, ∃ a, S.Reach θ a ∧ (S.NF a ∨ S.UN a) ∧ e = s(a, S.g c a) := by
  refine S.g_induction c (P := fun θ => ∀ e ∈ S.gEdges c θ,
    ∃ a, S.Reach θ a ∧ (S.NF a ∨ S.UN a) ∧ e = s(a, S.g c a)) (fun θ h ih => ?_)
    (fun θ h => ?_) θ
  · intro e he
    rw [S.gEdges_of_step c h, Finset.mem_insert] at he
    rcases he with rfl | he
    · exact ⟨θ, ReflTransGen.refl, h, rfl⟩
    · obtain ⟨a, ha, hna, rfl⟩ := ih e he
      exact ⟨a, (S.reach_g h).trans ha, hna, rfl⟩
  · intro e he
    rw [S.gEdges_of_isTerm c h] at he
    simp at he

theorem reach_mono {K K' : Finset (Sym2 V)} (h : K ⊆ K') {a b : V}
    (hr : FNE.EdgeCount.Reach K a b) : FNE.EdgeCount.Reach K' a b :=
  ReflTransGen.mono (fun _ _ hx => h hx) _ _ hr

theorem reach_symm {K : Finset (Sym2 V)} {a b : V} (hr : FNE.EdgeCount.Reach K a b) :
    FNE.EdgeCount.Reach K b a := by
  let _ : Std.Symm (fun x y : V => s(x, y) ∈ K) :=
    ⟨fun x y hxy => by rwa [Sym2.eq_swap]⟩
  exact (ReflTransGen.stdSymm (r := fun x y : V => s(x, y) ∈ K)).symm _ _ hr

/-- The greedy arm is connected from its start, and reaches its end. -/
theorem gEdges_reach (c : C) (θ : V) :
    (∀ e ∈ S.gEdges c θ, ∀ v ∈ e, FNE.EdgeCount.Reach (S.gEdges c θ) θ v) ∧
      FNE.EdgeCount.Reach (S.gEdges c θ) θ (S.gEnd c θ) := by
  refine S.g_induction c (P := fun θ =>
    (∀ e ∈ S.gEdges c θ, ∀ v ∈ e, FNE.EdgeCount.Reach (S.gEdges c θ) θ v) ∧
      FNE.EdgeCount.Reach (S.gEdges c θ) θ (S.gEnd c θ)) (fun θ h ih => ?_) (fun θ h => ?_) θ
  · obtain ⟨ih1, ih2⟩ := ih
    rw [S.gEnd_of_step c h, S.gEdges_of_step c h]
    have hsub : S.gEdges c (S.g c θ) ⊆ insert s(θ, S.g c θ) (S.gEdges c (S.g c θ)) :=
      Finset.subset_insert _ _
    have hstep : FNE.EdgeCount.Reach (insert s(θ, S.g c θ) (S.gEdges c (S.g c θ))) θ
        (S.g c θ) :=
      ReflTransGen.single (Finset.mem_insert_self _ _)
    refine ⟨fun e he v hv => ?_, hstep.trans (reach_mono hsub ih2)⟩
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact ReflTransGen.refl
      · exact hstep
    · exact hstep.trans (reach_mono hsub (ih1 e he v hv))
  · rw [S.gEnd_of_isTerm c h, S.gEdges_of_isTerm c h]
    exact ⟨fun e he => by simp at he, ReflTransGen.refl⟩

end Edges

/-! ## Poles -/

/-- A pole (a source of the copied-arm witness): a location and, for each charge, the first step
of its arm (`true`/`false`: which selected support). -/
structure Pole (V C : Type*) where
  /-- the location of the source -/
  loc : V
  /-- the first step of the arm of each charge -/
  fs : C → Bool

/-- The first vertex of the `c`-arm after the source. -/
def pFirst (σ : Pole V C) (c : C) : V := S.sup σ.loc (σ.fs c)

/-- The terminal leaf ending the `c`-arm. -/
def pEnd (σ : Pole V C) (c : C) : V := S.gEnd c (S.pFirst σ c)

/-- The group in which the `c`-arm ends. -/
def pGrp (σ : Pole V C) (c : C) : Γ := S.grp (S.pEnd σ c)

/-- The number of binary (positive support) edges of the `c`-arm, its first edge included. -/
def pBin (σ : Pole V C) (c : C) : ℕ := S.gBin c (S.pFirst σ c) + 1

/-- The number of edges of the `c`-arm (binary and unary). -/
def pLen (σ : Pole V C) (c : C) : ℕ := S.gLen c (S.pFirst σ c) + 1

/-- The edges of the `c`-arm. -/
def pEdges [DecidableEq V] (σ : Pole V C) (c : C) : Finset (Sym2 V) :=
  insert s(σ.loc, S.pFirst σ c) (S.gEdges c (S.pFirst σ c))

/-- The root pole: every first step is good. -/
def rootPole (ρ : V) : Pole V C := ⟨ρ, fun c => S.good c ρ⟩

/-- A valid pole: located at a binary vertex reached from the root. -/
def Valid (ρ : V) (σ : Pole V C) : Prop := S.Reach ρ σ.loc ∧ S.NF σ.loc

theorem pEnd_isTerm (σ : Pole V C) (c : C) : S.IsTerm (S.pEnd σ c) := S.gEnd_isTerm c _

theorem pGrp_term (σ : Pole V C) (c : C) : S.Term (S.pFirst σ c) (S.pGrp σ c) :=
  S.gEnd_term c _

theorem pGrp_term_root {ρ : V} {σ : Pole V C} (h : S.Valid ρ σ) (c : C) :
    S.Term ρ (S.pGrp σ c) :=
  S.term_trans h.1 (S.term_of_sup h.2 (S.pGrp_term σ c))

/-- Along an arm: `ψ_c(end) ≥ ψ_c(source) + ϱ₊·(binary edges) - (ϱ₊ + ϱ₋)·[first edge bad]`. -/
theorem pole_psi [Fintype C] {ψ : C → V → ℤ} {ϱp ϱm : ℤ} (hψ : S.IsPotential ψ ϱp ϱm)
    {σ : Pole V C} (h : S.NF σ.loc) (c : C) :
    ψ c σ.loc + ϱp * S.pBin σ c - (if σ.fs c = S.good c σ.loc then 0 else ϱp + ϱm) ≤
      ψ c (S.pEnd σ c) := by
  have h2 := S.gEnd_psi hψ c (S.pFirst σ c)
  unfold pEnd pBin
  push_cast
  by_cases hg : σ.fs c = S.good c σ.loc
  · have h1 : ψ c σ.loc + ϱp ≤ ψ c (S.pFirst σ c) := by
      have := hψ.2.1 σ.loc c h
      rw [← hg] at this
      exact this
    simp only [hg, ↓reduceIte]
    linarith
  · have h1 : ψ c σ.loc - ϱm ≤ ψ c (S.pFirst σ c) := hψ.2.2.1 σ.loc (σ.fs c) c h
    simp only [hg, ↓reduceIte]
    linarith

/-! ## Fronts and the splitting invariant -/

section Fronts

variable [DecidableEq V]

/-- Two group names both lie in `Φ(θ)` for one `θ ∈ W` ("descendant sets overlap"). -/
def Ov (W : Finset V) (a b : Γ) : Prop := ∃ θ ∈ W, S.Term θ a ∧ S.Term θ b

/-- The equivalence generated by `Ov W`: its classes are the descendant sets of the overlap
components of the front `W`. -/
def Rel (W : Finset V) : Γ → Γ → Prop := ReflTransGen (S.Ov W)

/-- The invariant: for every group `γ ∈ Φ(ρ)` and charge `c`, exactly one pole has its `c`-arm
ending in the class of `γ` ("exactly one arm endpoint of each charge in each frontier overlap
component"). -/
def Inv (ρ : V) (W : Finset V) (P : Finset (Pole V C)) : Prop :=
  ∀ γ, S.Term ρ γ → ∀ c, ∃! σ, σ ∈ P ∧ S.Rel W (S.pGrp σ c) γ

/-- Exposing a binary vertex: `(W \ {θ}) ∪ {θ⁽¹⁾, θ⁽²⁾}`. -/
def frontB (W : Finset V) (θ : V) : Finset V :=
  insert (S.sup θ true) (insert (S.sup θ false) (W.erase θ))

/-- Exposing a unary vertex: `(W \ {θ}) ∪ {un θ}`. -/
def frontU (W : Finset V) (θ : V) : Finset V := insert (S.un θ) (W.erase θ)

theorem rel_symm {W : Finset V} {a b : Γ} (h : S.Rel W a b) : S.Rel W b a := by
  let _ : Std.Symm (S.Ov W) := ⟨fun _ _ ⟨θ, hθ, h1, h2⟩ => ⟨θ, hθ, h2, h1⟩⟩
  exact (ReflTransGen.stdSymm (r := S.Ov W)).symm _ _ h

theorem rel_of_term {W : Finset V} {θ : V} {a b : Γ} (hθ : θ ∈ W) (ha : S.Term θ a)
    (hb : S.Term θ b) : S.Rel W a b :=
  ReflTransGen.single ⟨θ, hθ, ha, hb⟩

theorem mem_frontB_true (W : Finset V) (θ : V) : S.sup θ true ∈ S.frontB W θ :=
  Finset.mem_insert_self _ _

theorem mem_frontB_false (W : Finset V) (θ : V) : S.sup θ false ∈ S.frontB W θ :=
  Finset.mem_insert_of_mem (Finset.mem_insert_self _ _)

theorem rel_frontB_mono {W : Finset V} {θ : V} (hθW : θ ∈ W) (hθ : S.NF θ) {a b : Γ}
    (h : S.Rel (S.frontB W θ) a b) : S.Rel W a b := by
  refine ReflTransGen.mono (fun x y hxy => ?_) _ _ h
  obtain ⟨θ', hθ', h1, h2⟩ := hxy
  rcases Finset.mem_insert.mp hθ' with rfl | hθ'
  · exact ⟨θ, hθW, S.term_of_sup hθ h1, S.term_of_sup hθ h2⟩
  · rcases Finset.mem_insert.mp hθ' with rfl | hθ'
    · exact ⟨θ, hθW, S.term_of_sup hθ h1, S.term_of_sup hθ h2⟩
    · exact ⟨θ', Finset.mem_of_mem_erase hθ', h1, h2⟩

/-- A chain through the old front either survives in the new front, or both of its ends are
joined in the new front to groups of `Φ(θ)`. -/
theorem rel_split {W : Finset V} {θ : V} {x y : Γ} (h : S.Rel W x y) :
    S.Rel (S.frontB W θ) x y ∨
      ((∃ a, S.Term θ a ∧ S.Rel (S.frontB W θ) x a) ∧
        (∃ b, S.Term θ b ∧ S.Rel (S.frontB W θ) b y)) := by
  induction h with
  | refl => exact Or.inl ReflTransGen.refl
  | @tail y z _ hyz ih =>
    obtain ⟨θ', hθ', h1, h2⟩ := hyz
    by_cases he : θ' = θ
    · rw [he] at h1 h2
      refine Or.inr ⟨?_, z, h2, ReflTransGen.refl⟩
      rcases ih with h | ⟨ha, -⟩
      · exact ⟨y, h1, h⟩
      · exact ha
    · have hθ'F : θ' ∈ S.frontB W θ :=
        Finset.mem_insert_of_mem (Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he, hθ'⟩))
      have hyz' : S.Ov (S.frontB W θ) y z := ⟨θ', hθ'F, h1, h2⟩
      rcases ih with h | ⟨ha, b, hb, hby⟩
      · exact Or.inl (h.tail hyz')
      · exact Or.inr ⟨ha, b, hb, hby.tail hyz'⟩

/-- A unary exposure cannot split a component: the overlap relation is unchanged. -/
theorem ov_frontU {W : Finset V} {θ : V} (hθW : θ ∈ W) (hθ : S.UN θ) (a b : Γ) :
    S.Ov (S.frontU W θ) a b ↔ S.Ov W a b := by
  constructor
  · rintro ⟨θ', hθ', h1, h2⟩
    rcases Finset.mem_insert.mp hθ' with rfl | hθ'
    · exact ⟨θ, hθW, (S.term_un_iff hθ).2 h1, (S.term_un_iff hθ).2 h2⟩
    · exact ⟨θ', Finset.mem_of_mem_erase hθ', h1, h2⟩
  · rintro ⟨θ', hθ', h1, h2⟩
    by_cases he : θ' = θ
    · subst he
      exact ⟨S.un θ', Finset.mem_insert_self _ _, (S.term_un_iff hθ).1 h1,
        (S.term_un_iff hθ).1 h2⟩
    · exact ⟨θ', Finset.mem_insert_of_mem (Finset.mem_erase.mpr ⟨he, hθ'⟩), h1, h2⟩

theorem rel_frontU {W : Finset V} {θ : V} (hθW : θ ∈ W) (hθ : S.UN θ) :
    S.Rel (S.frontU W θ) = S.Rel W := by
  have : S.Ov (S.frontU W θ) = S.Ov W := by
    funext a b
    exact propext (S.ov_frontU hθW hθ a b)
  unfold Rel
  rw [this]

/-- One binary splitting step preserves the invariant, adding at most one pole (at `θ`): "When a
component splits, add a source at the split vertex. For each charge choose its initial support in
the new component lacking that charge endpoint." -/
theorem stepB_exists (ρ : V) {W : Finset V} {P : Finset (Pole V C)}
    (hW : ∀ θ ∈ W, S.Reach ρ θ) (hP : ∀ σ ∈ P, S.Valid ρ σ) (hinv : S.Inv ρ W P) {θ : V}
    (hθW : θ ∈ W) (hθ : S.NF θ) (c₀ : C) :
    ∃ P', P ⊆ P' ∧ (∀ σ ∈ P', S.Valid ρ σ) ∧ S.Inv ρ (S.frontB W θ) P' := by
  classical
  have hθ₁ := S.mem_frontB_true W θ
  have hθ₂ := S.mem_frontB_false W θ
  have mono : ∀ {a b : Γ}, S.Rel (S.frontB W θ) a b → S.Rel W a b :=
    fun h => S.rel_frontB_mono hθW hθ h
  have side : ∀ {a : Γ}, S.Term θ a → S.Term (S.sup θ true) a ∨ S.Term (S.sup θ false) a :=
    fun h => (S.term_sup_iff hθ).mp h
  by_cases hA : ∃ a b, S.Term (S.sup θ true) a ∧ S.Term (S.sup θ false) b ∧
      S.Rel (S.frontB W θ) a b
  · -- the component of `θ` does not split: no new pole
    obtain ⟨a₀, b₀, ha₀, hb₀, hab⟩ := hA
    have hjoin : ∀ {a b : Γ}, S.Term θ a → S.Term θ b → S.Rel (S.frontB W θ) a b := by
      intro a b ha hb
      rcases side ha with ha | ha <;> rcases side hb with hb | hb
      · exact S.rel_of_term hθ₁ ha hb
      · exact (S.rel_of_term hθ₁ ha ha₀).trans (hab.trans (S.rel_of_term hθ₂ hb₀ hb))
      · exact (S.rel_of_term hθ₂ ha hb₀).trans
          ((S.rel_symm hab).trans (S.rel_of_term hθ₁ ha₀ hb))
      · exact S.rel_of_term hθ₂ ha hb
    have heq : ∀ {x y : Γ}, S.Rel W x y → S.Rel (S.frontB W θ) x y := by
      intro x y h
      rcases S.rel_split h with h | ⟨⟨a, ha, hxa⟩, ⟨b, hb, hby⟩⟩
      · exact h
      · exact hxa.trans ((hjoin ha hb).trans hby)
    refine ⟨P, subset_rfl, hP, fun φ hφ c => ?_⟩
    obtain ⟨σ, ⟨hσ, hrσ⟩, huniq⟩ := hinv φ hφ c
    exact ⟨σ, ⟨hσ, heq hrσ⟩, fun σ' h => huniq σ' ⟨h.1, mono h.2⟩⟩
  · -- the component of `θ` splits in two: add a source at `θ`
    push Not at hA
    obtain ⟨φ₀, hφ₀⟩ := S.exists_term c₀ θ
    have hφ₀ρ : S.Term ρ φ₀ := S.term_trans (hW θ hθW) hφ₀
    have hex : ∀ c, ∃ σ, (σ ∈ P ∧ S.Rel W (S.pGrp σ c) φ₀) ∧
        ∀ σ', σ' ∈ P ∧ S.Rel W (S.pGrp σ' c) φ₀ → σ' = σ := fun c => hinv φ₀ hφ₀ρ c
    choose σc hσc huniq using hex
    let fs : C → Bool := fun c =>
      decide (¬ ∃ a, S.Term (S.sup θ true) a ∧ S.Rel (S.frontB W θ) (S.pGrp (σc c) c) a)
    let σn : Pole V C := ⟨θ, fs⟩
    refine ⟨insert σn P, Finset.subset_insert _ _, ?_, ?_⟩
    · intro σ hσ
      rcases Finset.mem_insert.mp hσ with rfl | hσ
      · exact ⟨hW θ hθW, hθ⟩
      · exact hP σ hσ
    intro φ hφ c
    have hnew : S.Term (S.sup θ (fs c)) (S.pGrp σn c) := S.pGrp_term σn c
    have hnewW : S.Rel W (S.pGrp σn c) φ₀ := S.rel_of_term hθW (S.term_of_sup hθ hnew) hφ₀
    have hxW : S.Rel W (S.pGrp (σc c) c) φ₀ := (hσc c).2
    by_cases hφ0 : S.Rel W φ φ₀
    · -- `φ` lies in the component that splits
      have hsideφ : ∃ a, S.Term θ a ∧ S.Rel (S.frontB W θ) φ a := by
        rcases S.rel_split hφ0 with h | ⟨h, -⟩
        · exact ⟨φ₀, hφ₀, h⟩
        · exact h
      have hsidex : ∃ a, S.Term θ a ∧ S.Rel (S.frontB W θ) (S.pGrp (σc c) c) a := by
        rcases S.rel_split hxW with h | ⟨h, -⟩
        · exact ⟨φ₀, hφ₀, h⟩
        · exact h
      have holdW' : ∀ σ', σ' ∈ P → S.Rel (S.frontB W θ) (S.pGrp σ' c) φ → σ' = σc c :=
        fun σ' h1 h2 => huniq c σ' ⟨h1, (mono h2).trans hφ0⟩
      obtain ⟨a, ha, hφa⟩ := hsideφ
      by_cases hx1 : ∃ a, S.Term (S.sup θ true) a ∧ S.Rel (S.frontB W θ) (S.pGrp (σc c) c) a
      · have hfs : fs c = false := decide_eq_false (not_not.mpr hx1)
        rw [hfs] at hnew
        obtain ⟨a₁, ha₁, hxa₁⟩ := hx1
        rcases side ha with ha | ha
        · refine ⟨σc c, ⟨Finset.mem_insert_of_mem (hσc c).1,
            hxa₁.trans ((S.rel_of_term hθ₁ ha₁ ha).trans (S.rel_symm hφa))⟩, ?_⟩
          rintro σ' ⟨hσ', h2⟩
          rcases Finset.mem_insert.mp hσ' with rfl | hσ'
          · exact absurd ((S.rel_symm hφa).trans (S.rel_symm h2)) (hA a _ ha hnew)
          · exact holdW' σ' hσ' h2
        · refine ⟨σn, ⟨Finset.mem_insert_self _ _,
            (S.rel_of_term hθ₂ hnew ha).trans (S.rel_symm hφa)⟩, ?_⟩
          rintro σ' ⟨hσ', h2⟩
          rcases Finset.mem_insert.mp hσ' with rfl | hσ'
          · rfl
          · have := holdW' σ' hσ' h2
            subst this
            exact absurd ((S.rel_symm hxa₁).trans (h2.trans hφa)) (hA a₁ a ha₁ ha)
      · have hfs : fs c = true := decide_eq_true hx1
        rw [hfs] at hnew
        obtain ⟨a', ha', hxa'⟩ := hsidex
        have ha'2 : S.Term (S.sup θ false) a' := by
          rcases side ha' with h | h
          · exact absurd ⟨a', h, hxa'⟩ hx1
          · exact h
        rcases side ha with ha | ha
        · refine ⟨σn, ⟨Finset.mem_insert_self _ _,
            (S.rel_of_term hθ₁ hnew ha).trans (S.rel_symm hφa)⟩, ?_⟩
          rintro σ' ⟨hσ', h2⟩
          rcases Finset.mem_insert.mp hσ' with rfl | hσ'
          · rfl
          · have := holdW' σ' hσ' h2
            subst this
            exact absurd ⟨a, ha, h2.trans hφa⟩ hx1
        · refine ⟨σc c, ⟨Finset.mem_insert_of_mem (hσc c).1,
            hxa'.trans ((S.rel_of_term hθ₂ ha'2 ha).trans (S.rel_symm hφa))⟩, ?_⟩
          rintro σ' ⟨hσ', h2⟩
          rcases Finset.mem_insert.mp hσ' with rfl | hσ'
          · exact absurd (h2.trans hφa) (hA _ a hnew ha)
          · exact holdW' σ' hσ' h2
    · -- `φ` lies in another component: nothing changes for it
      obtain ⟨σ0, ⟨hσ0, hr0⟩, hu0⟩ := hinv φ hφ c
      refine ⟨σ0, ⟨Finset.mem_insert_of_mem hσ0, ?_⟩, ?_⟩
      · rcases S.rel_split hr0 with h | ⟨-, b, hb, hbφ⟩
        · exact h
        · exact absurd ((S.rel_symm (mono hbφ)).trans (S.rel_of_term hθW hb hφ₀)) hφ0
      · rintro σ' ⟨hσ', h2⟩
        rcases Finset.mem_insert.mp hσ' with rfl | hσ'
        · exact absurd ((S.rel_symm (mono h2)).trans hnewW) hφ0
        · exact hu0 σ' ⟨hσ', mono h2⟩

/-- The measure `Σ_{θ ∈ W} 3^{rk θ}`, which every exposure decreases. -/
def meas (W : Finset V) : ℕ := ∑ θ ∈ W, 3 ^ S.rk θ

theorem sum_insert_le' (f : V → ℕ) (a : V) (s : Finset V) :
    ∑ x ∈ insert a s, f x ≤ f a + ∑ x ∈ s, f x := by
  by_cases ha : a ∈ s
  · rw [Finset.insert_eq_of_mem ha]
    omega
  · rw [Finset.sum_insert ha]

theorem meas_frontB_lt {W : Finset V} {θ : V} (hθW : θ ∈ W) (hθ : S.NF θ) :
    S.meas (S.frontB W θ) < S.meas W := by
  unfold meas frontB
  have h1 := sum_insert_le' (fun x => 3 ^ S.rk x) (S.sup θ true)
    (insert (S.sup θ false) (W.erase θ))
  have h2 := sum_insert_le' (fun x => 3 ^ S.rk x) (S.sup θ false) (W.erase θ)
  have h3 := Finset.add_sum_erase W (fun x => 3 ^ S.rk x) hθW
  have ht1 := S.rk_sup θ true hθ
  have ht2 := S.rk_sup θ false hθ
  obtain ⟨r, hr⟩ : ∃ r, S.rk θ = r + 1 := ⟨S.rk θ - 1, by omega⟩
  have e1 : 3 ^ S.rk (S.sup θ true) ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e2 : 3 ^ S.rk (S.sup θ false) ≤ 3 ^ r := Nat.pow_le_pow_right (by norm_num) (by omega)
  have e3 : 3 ^ S.rk θ = 3 * 3 ^ r := by rw [hr, pow_succ]; ring
  have hpos : 0 < 3 ^ r := by positivity
  omega

theorem meas_frontU_lt {W : Finset V} {θ : V} (hθW : θ ∈ W) (hθ : S.UN θ) :
    S.meas (S.frontU W θ) < S.meas W := by
  unfold meas frontU
  have h1 := sum_insert_le' (fun x => 3 ^ S.rk x) (S.un θ) (W.erase θ)
  have h3 := Finset.add_sum_erase W (fun x => 3 ^ S.rk x) hθW
  have e1 : 3 ^ S.rk (S.un θ) < 3 ^ S.rk θ :=
    Nat.pow_lt_pow_right (by norm_num) (S.rk_un θ hθ)
  omega

theorem frontB_reach {ρ : V} {W : Finset V} (hW : ∀ θ ∈ W, S.Reach ρ θ) {θ : V} (hθW : θ ∈ W)
    (hθ : S.NF θ) : ∀ θ' ∈ S.frontB W θ, S.Reach ρ θ' := by
  intro θ' h
  rcases Finset.mem_insert.mp h with rfl | h
  · exact (hW θ hθW).trans (S.reach_sup hθ true)
  · rcases Finset.mem_insert.mp h with rfl | h
    · exact (hW θ hθW).trans (S.reach_sup hθ false)
    · exact hW θ' (Finset.mem_of_mem_erase h)

theorem frontU_reach {ρ : V} {W : Finset V} (hW : ∀ θ ∈ W, S.Reach ρ θ) {θ : V} (hθW : θ ∈ W)
    (hθ : S.UN θ) : ∀ θ' ∈ S.frontU W θ, S.Reach ρ θ' := by
  intro θ' h
  rcases Finset.mem_insert.mp h with rfl | h
  · exact (hW θ hθW).trans (S.reach_un hθ)
  · exact hW θ' (Finset.mem_of_mem_erase h)

/-- Exposing until only terminal leaves remain gives poles in bijection with groups, for every
charge ("At the end each component is one terminal group"). -/
theorem exists_poles (ρ : V) (c₀ : C) : ∀ (n : ℕ) (W : Finset V) (P : Finset (Pole V C)),
    S.meas W = n → (∀ θ ∈ W, S.Reach ρ θ) → (∀ σ ∈ P, S.Valid ρ σ) → S.Inv ρ W P →
    ∃ P', P ⊆ P' ∧ (∀ σ ∈ P', S.Valid ρ σ) ∧
      ∀ γ, S.Term ρ γ → ∀ c, ∃! σ, σ ∈ P' ∧ S.pGrp σ c = γ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    intro W P hn hW hP hinv
    by_cases hexB : ∃ θ ∈ W, S.NF θ
    · obtain ⟨θ, hθW, hθ⟩ := hexB
      obtain ⟨P₁, hP₁, hv₁, hinv₁⟩ := S.stepB_exists ρ hW hP hinv hθW hθ c₀
      obtain ⟨P', hP', hv', hfin⟩ := ih _ (hn ▸ S.meas_frontB_lt hθW hθ) (S.frontB W θ) P₁ rfl
        (S.frontB_reach hW hθW hθ) hv₁ hinv₁
      exact ⟨P', hP₁.trans hP', hv', hfin⟩
    · by_cases hexU : ∃ θ ∈ W, S.UN θ
      · obtain ⟨θ, hθW, hθ⟩ := hexU
        have hinv₁ : S.Inv ρ (S.frontU W θ) P := by
          intro γ hγ c
          rw [S.rel_frontU hθW hθ]
          exact hinv γ hγ c
        exact ih _ (hn ▸ S.meas_frontU_lt hθW hθ) (S.frontU W θ) P rfl
          (S.frontU_reach hW hθW hθ) hP hinv₁
      · push Not at hexB hexU
        have hov : ∀ a b, S.Ov W a b → a = b := by
          rintro a b ⟨θ, hθ, ha, hb⟩
          have ht : S.IsTerm θ := ⟨hexB θ hθ, hexU θ hθ⟩
          rw [← (S.term_isTerm_iff ht).1 ha, ← (S.term_isTerm_iff ht).1 hb]
        have hrel : ∀ {x y : Γ}, S.Rel W x y → x = y := by
          intro x y h
          induction h with
          | refl => rfl
          | tail _ hyz ih => exact ih.trans (hov _ _ hyz)
        refine ⟨P, subset_rfl, hP, fun φ hφ c => ?_⟩
        obtain ⟨σ, ⟨hσ, hrσ⟩, huniq⟩ := hinv φ hφ c
        exact ⟨σ, ⟨hσ, hrel hrσ⟩, fun σ' h => huniq σ' ⟨h.1, h.2 ▸ ReflTransGen.refl⟩⟩

/-- Poles in bijection with groups: a finite set of valid poles containing the root pole such that,
for every group `γ ∈ Φ(ρ)` and every charge `c`, exactly one pole has its `c`-arm ending in
`γ`. -/
theorem exists_bij {ρ : V} (hρ : S.NF ρ) (c₀ : C) :
    ∃ P : Finset (Pole V C), S.rootPole ρ ∈ P ∧ (∀ σ ∈ P, S.Valid ρ σ) ∧
      ∀ γ, S.Term ρ γ → ∀ c, ∃! σ, σ ∈ P ∧ S.pGrp σ c = γ := by
  classical
  have hroot : S.Valid ρ (S.rootPole ρ) := ⟨ReflTransGen.refl, hρ⟩
  have hinv : S.Inv ρ {ρ} {S.rootPole ρ} := by
    intro γ hγ c
    refine ⟨S.rootPole ρ, ⟨Finset.mem_singleton_self _, ?_⟩, fun σ h => ?_⟩
    · exact S.rel_of_term (Finset.mem_singleton_self ρ) (S.pGrp_term_root hroot c) hγ
    · exact Finset.mem_singleton.mp h.1
  obtain ⟨P, hP, hv, hbij⟩ := S.exists_poles ρ c₀ _ {ρ} {S.rootPole ρ} rfl
    (fun θ h => by rw [Finset.mem_singleton.mp h]; exact ReflTransGen.refl) (fun σ h => by
      rw [Finset.mem_singleton.mp h]; exact hroot) hinv
  exact ⟨P, hP (Finset.mem_singleton_self _), hv, hbij⟩

end Fronts

/-! ## The grouped terminal estimate -/

/-- Two poles of `P` are linked if an arm of one and an arm of the other end in one group. -/
def Linked (P : Finset (Pole V C)) (σ σ' : Pole V C) : Prop :=
  σ ∈ P ∧ σ' ∈ P ∧ ∃ c c', S.pGrp σ c = S.pGrp σ' c'

/-- **Lemma 5.1** (grouped terminal estimate). Let the potentials sum to zero, gain at least `ϱ₊`
along good edges and lose at most `ϱ₋` along any edge (`ϱ₊ + ϱ₋ ≥ 0`), with unary links of zero
potential change, and let the five potential oscillations within any group sum to at most `Ω`
(`hosc`: for any terminal leaves `φ c`, `φ' c` of one group, `Σ_c ψ_c(φ c) - ψ_c(φ' c) ≤ Ω`).
For a binary root `ρ` there is a set `P` of `g = |P|` sources containing the root source, each
linked to the root through shared groups, such that for every charge the arms of `P` end in `g`
distinct groups, the same groups for every charge, and the number `e` of binary edges of the arms,
counted with multiplicity, satisfies `ϱ₊ e ≤ (ϱ₊ + ϱ₋)·|C|·(g - 1) + Ωg`. -/
theorem grouped_terminal_estimate [DecidableEq V] [Fintype C] [Nonempty C] {ψ : C → V → ℤ}
    {ϱp ϱm Ω : ℤ} (hψ : S.IsPotential ψ ϱp ϱm) (hpm : 0 ≤ ϱp + ϱm)
    (hosc : ∀ φ φ' : C → V, (∀ c, S.IsTerm (φ c)) → (∀ c, S.IsTerm (φ' c)) →
      (∀ c c', S.grp (φ c) = S.grp (φ' c')) → ∑ c, (ψ c (φ c) - ψ c (φ' c)) ≤ Ω)
    {ρ : V} (hρ : S.NF ρ) :
    ∃ P : Finset (Pole V C), S.rootPole ρ ∈ P ∧ (∀ σ ∈ P, S.Valid ρ σ) ∧
      (∀ σ ∈ P, ReflTransGen (S.Linked P) (S.rootPole ρ) σ) ∧
      (∀ c, ∀ σ ∈ P, ∀ σ' ∈ P, S.pGrp σ c = S.pGrp σ' c → σ = σ') ∧
      (∀ σ ∈ P, ∀ c c', ∃ σ' ∈ P, S.pGrp σ' c' = S.pGrp σ c) ∧
      ϱp * ∑ σ ∈ P, ∑ c, (S.pBin σ c : ℤ) ≤
        (ϱp + ϱm) * Fintype.card C * ((P.card : ℤ) - 1) + Ω * P.card := by
  classical
  obtain ⟨c₀⟩ := (inferInstance : Nonempty C)
  obtain ⟨P, hrootP, hvalid, hbij⟩ := S.exists_bij hρ c₀
  set Pρ := P.filter (fun σ => ReflTransGen (S.Linked P) (S.rootPole ρ) σ) with hPρ
  have hroot : S.rootPole ρ ∈ Pρ := Finset.mem_filter.mpr ⟨hrootP, ReflTransGen.refl⟩
  have hPρP : ∀ σ ∈ Pρ, σ ∈ P := fun σ h => (Finset.mem_filter.mp h).1
  have hPρC : ∀ σ ∈ Pρ, ReflTransGen (S.Linked P) (S.rootPole ρ) σ :=
    fun σ h => (Finset.mem_filter.mp h).2
  have hNF : ∀ σ ∈ Pρ, S.NF σ.loc := fun σ h => (hvalid σ (hPρP σ h)).2
  have hinj : ∀ c, ∀ σ ∈ P, ∀ σ' ∈ P, S.pGrp σ c = S.pGrp σ' c → σ = σ' := by
    intro c σ hσ σ' hσ' h
    obtain ⟨τ, -, hτ⟩ := hbij _ (S.pGrp_term_root (hvalid σ hσ) c) c
    exact (hτ σ ⟨hσ, rfl⟩).trans (hτ σ' ⟨hσ', h.symm⟩).symm
  have hsurj : ∀ σ ∈ Pρ, ∀ c c', ∃ σ' ∈ Pρ, S.pGrp σ' c' = S.pGrp σ c := by
    intro σ hσ c c'
    obtain ⟨τ, ⟨hτP, hτe⟩, -⟩ := hbij _ (S.pGrp_term_root (hvalid σ (hPρP σ hσ)) c) c'
    exact ⟨τ, Finset.mem_filter.mpr ⟨hτP, (hPρC σ hσ).tail ⟨hPρP σ hσ, hτP, c, c', hτe.symm⟩⟩,
      hτe⟩
  -- linking inside `Pρ`
  have hlinkρ : ∀ σ ∈ Pρ, ReflTransGen (S.Linked Pρ) (S.rootPole ρ) σ := by
    intro σ hσ
    have key : ∀ τ, ReflTransGen (S.Linked P) (S.rootPole ρ) τ →
        ReflTransGen (S.Linked Pρ) (S.rootPole ρ) τ := by
      intro τ h
      induction h with
      | refl => exact ReflTransGen.refl
      | @tail b τ' hrb hbτ ih =>
        obtain ⟨hbP, hτ'P, c, c', hend⟩ := hbτ
        refine ih.tail ⟨Finset.mem_filter.mpr ⟨hbP, hrb⟩,
          Finset.mem_filter.mpr ⟨hτ'P, hrb.tail ⟨hbP, hτ'P, c, c', hend⟩⟩, c, c', hend⟩
    exact key σ (hPρC σ hσ)
  -- the groups
  set G := Pρ.image (fun σ => S.pGrp σ c₀) with hG
  have himage : ∀ c, Pρ.image (fun σ => S.pGrp σ c) = G := by
    have key : ∀ c c', Pρ.image (fun σ => S.pGrp σ c) ⊆ Pρ.image (fun σ => S.pGrp σ c') := by
      intro c c' γ hγ
      obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hγ
      obtain ⟨τ, hτ, hτe⟩ := hsurj σ hσ c c'
      exact Finset.mem_image.mpr ⟨τ, hτ, hτe⟩
    intro c
    exact Finset.Subset.antisymm (key c c₀) (key c₀ c)
  have hinjρ : ∀ c, Set.InjOn (fun σ => S.pGrp σ c) (Pρ : Set (Pole V C)) :=
    fun c σ hσ σ' hσ' h => hinj c σ (hPρP σ hσ) σ' (hPρP σ' hσ') h
  have hcardG : G.card = Pρ.card := Finset.card_image_of_injOn (hinjρ c₀)
  have hinv : ∀ c, ∀ γ ∈ G, ∃ σ ∈ Pρ, S.pGrp σ c = γ := by
    intro c γ hγ
    rw [← himage c] at hγ
    obtain ⟨σ, hσ, h⟩ := Finset.mem_image.mp hγ
    exact ⟨σ, hσ, h⟩
  have : Nonempty (Pole V C) := ⟨S.rootPole ρ⟩
  choose! inv hinvP hinvG using hinv
  have hinv_self : ∀ c, ∀ σ ∈ Pρ, inv c (S.pGrp σ c) = σ := by
    intro c σ hσ
    have hγ : S.pGrp σ c ∈ G := by
      rw [← himage c]
      exact Finset.mem_image_of_mem _ hσ
    exact hinj c _ (hPρP _ (hinvP c _ hγ)) σ (hPρP σ hσ) (hinvG c _ hγ)
  -- the terminal sum: at most `Ω` per group
  have hgrp : ∀ γ ∈ G, ∑ c, ψ c (S.pEnd (inv c γ) c) ≤ Ω := by
    intro γ hγ
    have h := hosc (fun c => S.pEnd (inv c γ) c) (fun _ => S.pEnd (inv c₀ γ) c₀)
      (fun c => S.pEnd_isTerm _ c) (fun _ => S.pEnd_isTerm _ c₀) (fun c _ => by
        change S.pGrp (inv c γ) c = S.pGrp (inv c₀ γ) c₀
        rw [hinvG c γ hγ, hinvG c₀ γ hγ])
    rw [Finset.sum_sub_distrib, hψ.1, sub_zero] at h
    exact h
  have hT : ∑ σ ∈ Pρ, ∑ c, ψ c (S.pEnd σ c) ≤ Ω * Pρ.card := by
    rw [Finset.sum_comm]
    have e1 : ∀ c, ∑ σ ∈ Pρ, ψ c (S.pEnd σ c) = ∑ γ ∈ G, ψ c (S.pEnd (inv c γ) c) := by
      intro c
      rw [← himage c, Finset.sum_image (hinjρ c)]
      refine Finset.sum_congr rfl (fun σ hσ => ?_)
      rw [hinv_self c σ hσ]
    simp only [e1]
    rw [Finset.sum_comm]
    calc ∑ γ ∈ G, ∑ c, ψ c (S.pEnd (inv c γ) c) ≤ ∑ _γ ∈ G, Ω := Finset.sum_le_sum hgrp
      _ = Ω * Pρ.card := by rw [Finset.sum_const, hcardG, nsmul_eq_mul]; ring
  -- the source sum vanishes
  have hB : ∑ σ ∈ Pρ, ∑ c, ψ c σ.loc = 0 := Finset.sum_eq_zero (fun σ _ => hψ.1 σ.loc)
  -- the arms
  have harm : ϱp * ∑ σ ∈ Pρ, ∑ c, (S.pBin σ c : ℤ) -
      ∑ σ ∈ Pρ, ∑ c, (if σ.fs c = S.good c σ.loc then (0 : ℤ) else ϱp + ϱm) ≤
        ∑ σ ∈ Pρ, ∑ c, ψ c (S.pEnd σ c) := by
    have h1 : ∀ σ ∈ Pρ, ∀ c, ϱp * (S.pBin σ c : ℤ) -
        (if σ.fs c = S.good c σ.loc then (0 : ℤ) else ϱp + ϱm) ≤
          ψ c (S.pEnd σ c) - ψ c σ.loc := by
      intro σ hσ c
      have := S.pole_psi hψ (hNF σ hσ) c
      linarith
    calc ϱp * ∑ σ ∈ Pρ, ∑ c, (S.pBin σ c : ℤ) -
          ∑ σ ∈ Pρ, ∑ c, (if σ.fs c = S.good c σ.loc then (0 : ℤ) else ϱp + ϱm) =
          ∑ σ ∈ Pρ, ∑ c, (ϱp * (S.pBin σ c : ℤ) -
            (if σ.fs c = S.good c σ.loc then (0 : ℤ) else ϱp + ϱm)) := by
          simp only [Finset.mul_sum, Finset.sum_sub_distrib]
      _ ≤ ∑ σ ∈ Pρ, ∑ c, (ψ c (S.pEnd σ c) - ψ c σ.loc) :=
          Finset.sum_le_sum (fun σ hσ => Finset.sum_le_sum (fun c _ => h1 σ hσ c))
      _ = ∑ σ ∈ Pρ, ∑ c, ψ c (S.pEnd σ c) - ∑ σ ∈ Pρ, ∑ c, ψ c σ.loc := by
          simp only [Finset.sum_sub_distrib]
      _ = ∑ σ ∈ Pρ, ∑ c, ψ c (S.pEnd σ c) := by rw [hB, sub_zero]
  -- only first edges of nonroot sources can be bad
  have hbad : ∑ σ ∈ Pρ, ∑ c, (if σ.fs c = S.good c σ.loc then (0 : ℤ) else ϱp + ϱm) ≤
      (ϱp + ϱm) * Fintype.card C * ((Pρ.card : ℤ) - 1) := by
    rw [← Finset.add_sum_erase _ _ hroot]
    have hr : ∑ c, (if (S.rootPole ρ).fs c = S.good c (S.rootPole ρ).loc then (0 : ℤ)
        else ϱp + ϱm) = 0 :=
      Finset.sum_eq_zero (fun c _ => by simp [rootPole])
    rw [hr, zero_add]
    have hone : ∀ σ ∈ Pρ.erase (S.rootPole ρ),
        ∑ c, (if σ.fs c = S.good c σ.loc then (0 : ℤ) else ϱp + ϱm) ≤
          (ϱp + ϱm) * Fintype.card C := by
      intro σ _
      calc ∑ c, (if σ.fs c = S.good c σ.loc then (0 : ℤ) else ϱp + ϱm) ≤ ∑ _c : C, (ϱp + ϱm) :=
            Finset.sum_le_sum (fun c _ => by split_ifs <;> linarith)
        _ = (ϱp + ϱm) * Fintype.card C := by
            rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]; ring
    calc _ ≤ ∑ _σ ∈ Pρ.erase (S.rootPole ρ), (ϱp + ϱm) * (Fintype.card C : ℤ) :=
          Finset.sum_le_sum hone
      _ = (ϱp + ϱm) * Fintype.card C * ((Pρ.card : ℤ) - 1) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem hroot, nsmul_eq_mul]
          have : 1 ≤ Pρ.card := Finset.card_pos.mpr ⟨_, hroot⟩
          push_cast [Nat.cast_sub this]
          ring
  refine ⟨Pρ, hroot, fun σ hσ => hvalid σ (hPρP σ hσ), hlinkρ,
    fun c σ hσ σ' hσ' h => hinj c σ (hPρP σ hσ) σ' (hPρP σ' hσ') h, hsurj, ?_⟩
  linarith

/-! ## The copied-arm witness -/

section Witness

variable [DecidableEq V] [Fintype C]

/-- The arm edges of the sources `P`. -/
def armEdges (P : Finset (Pole V C)) : Finset (Sym2 V) :=
  P.biUnion (fun σ => Finset.univ.biUnion (fun c => S.pEdges σ c))

open Classical in
/-- The identification links between arm ends in one group ("merge leaves by group name"). -/
def grpEdges (P : Finset (Pole V C)) : Finset (Sym2 V) :=
  (((P ×ˢ (Finset.univ : Finset C)) ×ˢ (P ×ˢ (Finset.univ : Finset C))).filter
    (fun p => S.pGrp p.1.1 p.1.2 = S.pGrp p.2.1 p.2.2)).image
    (fun p => s(S.pEnd p.1.1 p.1.2, S.pEnd p.2.1 p.2.2))

/-- The copied-arm witness. -/
def witness (P : Finset (Pole V C)) : Finset (Sym2 V) := S.armEdges P ∪ S.grpEdges P

theorem pEdges_reach (σ : Pole V C) (c : C) :
    (∀ e ∈ S.pEdges σ c, ∀ v ∈ e, FNE.EdgeCount.Reach (S.pEdges σ c) σ.loc v) ∧
      FNE.EdgeCount.Reach (S.pEdges σ c) σ.loc (S.pEnd σ c) := by
  obtain ⟨h1, h2⟩ := S.gEdges_reach c (S.pFirst σ c)
  have hsub : S.gEdges c (S.pFirst σ c) ⊆ S.pEdges σ c := Finset.subset_insert _ _
  have hstep : FNE.EdgeCount.Reach (S.pEdges σ c) σ.loc (S.pFirst σ c) :=
    ReflTransGen.single (Finset.mem_insert_self _ _)
  refine ⟨fun e he v hv => ?_, hstep.trans (reach_mono hsub h2)⟩
  rcases Finset.mem_insert.mp he with rfl | he
  · rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact ReflTransGen.refl
    · exact hstep
  · exact hstep.trans (reach_mono hsub (h1 e he v hv))

theorem pEdges_card_le (σ : Pole V C) (c : C) : (S.pEdges σ c).card ≤ S.pLen σ c :=
  (Finset.card_insert_le _ _).trans (Nat.add_le_add_right (S.gEdges_card_le c _) 1)

/-- The arm edges number at most the arm lengths, counted with multiplicity. -/
theorem armEdges_card_le (P : Finset (Pole V C)) :
    (S.armEdges P).card ≤ ∑ σ ∈ P, ∑ c, S.pLen σ c :=
  Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun σ _ =>
    Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun c _ => S.pEdges_card_le σ c))))

theorem pEdges_subset_witness {P : Finset (Pole V C)} {σ : Pole V C} (hσ : σ ∈ P) (c : C) :
    S.pEdges σ c ⊆ S.witness P := fun _ he =>
  Finset.mem_union_left _
    (Finset.mem_biUnion.mpr ⟨σ, hσ, Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, he⟩⟩)

theorem grpEdge_mem_witness {P : Finset (Pole V C)} {σ σ' : Pole V C} (hσ : σ ∈ P)
    (hσ' : σ' ∈ P) {c c' : C} (h : S.pGrp σ c = S.pGrp σ' c') :
    s(S.pEnd σ c, S.pEnd σ' c') ∈ S.witness P := by
  classical
  refine Finset.mem_union_right _ (Finset.mem_image.mpr ⟨((σ, c), (σ', c')), ?_, rfl⟩)
  refine Finset.mem_filter.mpr ⟨?_, h⟩
  simp [hσ, hσ']

/-- **The copied-arm witness is connected at the root**: every end of every edge of the witness of
a set of sources linked to the root pole is reached from the root inside the witness. -/
theorem witness_connected {ρ : V} {P : Finset (Pole V C)}
    (hlink : ∀ σ ∈ P, ReflTransGen (S.Linked P) (S.rootPole ρ) σ) :
    FNE.EdgeCount.ConnectedAt (S.witness P) ρ := by
  classical
  have hloc : ∀ σ, ReflTransGen (S.Linked P) (S.rootPole ρ) σ →
      FNE.EdgeCount.Reach (S.witness P) ρ σ.loc := by
    intro σ h
    induction h with
    | refl => exact ReflTransGen.refl
    | @tail b σ' _ hbσ ih =>
      obtain ⟨hbP, hσ'P, c, c', hend⟩ := hbσ
      have h1 := reach_mono (S.pEdges_subset_witness hbP c) (S.pEdges_reach b c).2
      have h2 := reach_symm (reach_mono (S.pEdges_subset_witness hσ'P c')
        (S.pEdges_reach σ' c').2)
      have h3 : FNE.EdgeCount.Reach (S.witness P) (S.pEnd b c) (S.pEnd σ' c') :=
        ReflTransGen.single (S.grpEdge_mem_witness hbP hσ'P hend)
      exact ih.trans (h1.trans (h3.trans h2))
  have hend : ∀ σ ∈ P, ∀ c, FNE.EdgeCount.Reach (S.witness P) ρ (S.pEnd σ c) := fun σ hσ c =>
    (hloc σ (hlink σ hσ)).trans
      (reach_mono (S.pEdges_subset_witness hσ c) (S.pEdges_reach σ c).2)
  intro e he v hv
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨σ, hσ, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨c, -, he⟩ := Finset.mem_biUnion.mp he
    exact (hloc σ (hlink σ hσ)).trans
      (reach_mono (S.pEdges_subset_witness hσ c) ((S.pEdges_reach σ c).1 e he v hv))
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    have hp' := (Finset.mem_filter.mp hp).1
    simp only [Finset.mem_product, Finset.mem_univ, and_true] at hp'
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact hend _ hp'.1 _
    · exact hend _ hp'.2 _

/-- The root is an end of a witness edge. -/
theorem root_mem_witness {ρ : V} {P : Finset (Pole V C)} (hroot : S.rootPole ρ ∈ P)
    [Nonempty C] : ∃ e ∈ S.witness P, ρ ∈ e := by
  obtain ⟨c⟩ := (inferInstance : Nonempty C)
  exact ⟨_, S.pEdges_subset_witness hroot c (Finset.mem_insert_self _ _), Sym2.mem_mk_left _ _⟩

end Witness

/-! ## Singleton groups -/

/-- **Lemma 5.1, singleton groups**: if the bound holds with `Ω = 0` and `ϱ₊ > 0`, a binary root
has at least two sources, hence at least two distinct terminal groups ("for a nonterminal root
`e > 0`, so singleton groups require `g ≥ 2`"). -/
theorem two_le_card_of_bound [Fintype C] [Nonempty C] {ϱp ϱm : ℤ} (hp : 0 < ϱp)
    {P : Finset (Pole V C)} {ρ : V} (hroot : S.rootPole ρ ∈ P)
    (hb : ϱp * ∑ σ ∈ P, ∑ c, (S.pBin σ c : ℤ) ≤
      (ϱp + ϱm) * Fintype.card C * ((P.card : ℤ) - 1) + 0 * P.card) :
    2 ≤ P.card := by
  by_contra hlt
  push Not at hlt
  have h1 : P.card = 1 := le_antisymm (by omega) (Finset.card_pos.mpr ⟨_, hroot⟩)
  rw [h1] at hb
  have hpos : (1 : ℤ) ≤ ∑ σ ∈ P, ∑ c, (S.pBin σ c : ℤ) := by
    obtain ⟨c⟩ := (inferInstance : Nonempty C)
    have hnn : ∀ σ ∈ P, ∀ c, (0 : ℤ) ≤ S.pBin σ c := fun _ _ _ => Nat.cast_nonneg _
    calc (1 : ℤ) ≤ S.pBin (S.rootPole ρ) c := by unfold pBin; push_cast; omega
      _ ≤ ∑ c, (S.pBin (S.rootPole ρ) c : ℤ) :=
          Finset.single_le_sum (f := fun c => (S.pBin (S.rootPole ρ) c : ℤ))
            (fun c _ => hnn _ hroot c) (Finset.mem_univ c)
      _ ≤ ∑ σ ∈ P, ∑ c, (S.pBin σ c : ℤ) :=
          Finset.single_le_sum (f := fun σ => ∑ c, (S.pBin σ c : ℤ))
            (fun σ hσ => Finset.sum_nonneg (fun c _ => hnn σ hσ c)) hroot
  push_cast at hb
  nlinarith

/-! ## Singleton groups, directly -/

/-- With singleton groups (the group name determines the terminal leaf), the five potential
oscillations within any group vanish: `hosc` holds with `Ω = 0`. -/
theorem hosc_singleton [Fintype C] {ψ : C → V → ℤ}
    (hinj : ∀ φ φ', S.IsTerm φ → S.IsTerm φ' → S.grp φ = S.grp φ' → φ = φ') :
    ∀ φ φ' : C → V, (∀ c, S.IsTerm (φ c)) → (∀ c, S.IsTerm (φ' c)) →
      (∀ c c', S.grp (φ c) = S.grp (φ' c')) → ∑ c, (ψ c (φ c) - ψ c (φ' c)) ≤ 0 := by
  intro φ φ' h h' hg
  refine le_of_eq (Finset.sum_eq_zero (fun c _ => ?_))
  rw [hinj _ _ (h c) (h' c) (hg c c), sub_self]

/-- **Lemma 5.1, singleton groups**: "With singleton groups a nonterminal root has at least two
terminal flags": the selected sources, hence the selected groups, number at least two. -/
theorem singleton_two_le [DecidableEq V] [Fintype C] [Nonempty C] {ψ : C → V → ℤ}
    {ϱp ϱm : ℤ} (hψ : S.IsPotential ψ ϱp ϱm) (hp : 0 < ϱp) (hpm : 0 ≤ ϱp + ϱm)
    (hinj : ∀ φ φ', S.IsTerm φ → S.IsTerm φ' → S.grp φ = S.grp φ' → φ = φ')
    {ρ : V} (hρ : S.NF ρ) :
    ∃ P : Finset (Pole V C), S.rootPole ρ ∈ P ∧ (∀ σ ∈ P, S.Valid ρ σ) ∧
      (∀ c, ∀ σ ∈ P, ∀ σ' ∈ P, S.pGrp σ c = S.pGrp σ' c → σ = σ') ∧ 2 ≤ P.card := by
  obtain ⟨P, hr, hv, -, hi, -, hb⟩ :=
    S.grouped_terminal_estimate hψ hpm (S.hosc_singleton hinj) hρ
  exact ⟨P, hr, hv, hi, S.two_le_card_of_bound hp hr hb⟩

/-! ## The span -/

section Span

variable [DecidableEq V]

/-- An edge crosses one time level: it joins times `T + 1` and `T`. -/
def Crossing (time : V → ℤ) (e : Sym2 V) : Prop := ∃ a b, e = s(a, b) ∧ time b + 1 = time a

open Classical in
/-- If every edge of `K` crosses one time level or joins equal times, then reaching `y` from `x`
inside `K` crosses every level between them by its own crossing edge (the forgetting core's
`time_le_of_edgeReach`, with time-preserving edges allowed). -/
theorem time_le_of_edgeReach (time : V → ℤ) (K : Finset (Sym2 V))
    (hK : ∀ e ∈ K, Crossing time e ∨ ∃ a b, e = s(a, b) ∧ time a = time b) {x y : V}
    (h : FNE.EdgeCount.Reach K x y) :
    time x ≤ time y + ((K.filter (Crossing time)).card : ℤ) := by
  classical
  have cross : ∀ T : ℤ, time y ≤ T → T < time x →
      ∃ a b, s(a, b) ∈ K ∧ time a = T + 1 ∧ time b = T := by
    intro T
    induction h with
    | refl => intro h1 h2; omega
    | @tail z w _ hzw ih =>
      intro h1 h2
      by_cases hz : time z ≤ T
      · exact ih hz h2
      · rcases hK _ hzw with ⟨a, b, hab, hba⟩ | ⟨a, b, hab, hba⟩
        · rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
          · exact ⟨z, w, hzw, by omega, by omega⟩
          · omega
        · rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
  by_cases hxy : time x ≤ time y
  · have : (0 : ℤ) ≤ ((K.filter (Crossing time)).card : ℤ) := Nat.cast_nonneg _
    omega
  have : Nonempty V := ⟨x⟩
  have hc : ∀ T ∈ Finset.Ico (time y) (time x), ∃ ab : V × V,
      s(ab.1, ab.2) ∈ K ∧ time ab.1 = T + 1 ∧ time ab.2 = T := by
    intro T hT
    obtain ⟨h1, h2⟩ := Finset.mem_Ico.mp hT
    obtain ⟨a, b, h⟩ := cross T h1 h2
    exact ⟨(a, b), h⟩
  choose! f hf using hc
  have hle := Finset.card_le_card_of_injOn (fun T => s((f T).1, (f T).2))
    (t := K.filter (Crossing time))
    (fun T hT => Finset.mem_filter.mpr ⟨(hf T hT).1, (f T).1, (f T).2, rfl, by
      have := hf T hT; omega⟩) (by
      intro T hT T' hT' heq
      have h1 := hf T hT
      have h2 := hf T' hT'
      rcases Sym2.eq_iff.mp heq with ⟨ha, hb⟩ | ⟨ha, hb⟩
      · have := congrArg time hb
        omega
      · have e1 := congrArg time ha
        have e2 := congrArg time hb
        omega)
  rw [Int.card_Ico] at hle
  omega

open Classical in
/-- Along a greedy arm the crossing edges are binary, at most `gBin` of them, when unary links
preserve time. -/
theorem gEdges_crossing_card_le (time : V → ℤ) (hun : ∀ θ, S.UN θ → time (S.un θ) = time θ)
    (c : C) (θ : V) : ((S.gEdges c θ).filter (Crossing time)).card ≤ S.gBin c θ := by
  classical
  refine S.g_induction c (P := fun θ => ((S.gEdges c θ).filter (Crossing time)).card ≤
    S.gBin c θ) (fun θ h ih => ?_) (fun θ h => ?_) θ
  · rw [S.gEdges_of_step c h, Finset.filter_insert]
    rcases h with h | h
    · rw [S.gBin_of_NF c h]
      split_ifs
      · exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right ih 1)
      · omega
    · rw [S.gBin_of_UN c h]
      have hnc : ¬ Crossing time s(θ, S.g c θ) := by
        rintro ⟨a, b, hab, hba⟩
        have ht := hun θ h
        rw [S.g_of_UN h] at hab
        rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
      simp only [hnc, ↓reduceIte]
      exact ih
  · rw [S.gEdges_of_isTerm c h]
    simp

variable [Fintype C]

open Classical in
/-- The crossing edges of the arms number at most `e`, the binary arm edges counted with
multiplicity. -/
theorem armEdges_crossing_card_le (time : V → ℤ) (hun : ∀ θ, S.UN θ → time (S.un θ) = time θ)
    (P : Finset (Pole V C)) :
    ((S.armEdges P).filter (Crossing time)).card ≤ ∑ σ ∈ P, ∑ c, S.pBin σ c := by
  classical
  unfold armEdges
  rw [Finset.filter_biUnion]
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun σ _ => ?_))
  rw [Finset.filter_biUnion]
  refine Finset.card_biUnion_le.trans (Finset.sum_le_sum (fun c _ => ?_))
  unfold pEdges pBin
  rw [Finset.filter_insert]
  have := S.gEdges_crossing_card_le time hun c (S.pFirst σ c)
  split_ifs
  · exact (Finset.card_insert_le _ _).trans (Nat.add_le_add_right this 1)
  · omega

/-- Every vertex of a witness edge is reached from the root in the graph. -/
theorem witness_reach {ρ : V} {P : Finset (Pole V C)} (hvalid : ∀ σ ∈ P, S.Valid ρ σ) :
    ∀ e ∈ S.witness P, ∀ v ∈ e, S.Reach ρ v := by
  classical
  have harm : ∀ σ ∈ P, ∀ c, ∀ e ∈ S.pEdges σ c, ∀ v ∈ e, S.Reach ρ v := by
    intro σ hσ c e he v hv
    have hloc := (hvalid σ hσ).1
    have hfirst : S.Reach ρ (S.pFirst σ c) := hloc.trans (S.reach_sup (hvalid σ hσ).2 _)
    rcases Finset.mem_insert.mp he with rfl | he
    · rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact hloc
      · exact hfirst
    · obtain ⟨a, ha, hna, rfl⟩ := S.gEdges_spec c _ e he
      rcases Sym2.mem_iff.mp hv with rfl | rfl
      · exact hfirst.trans ha
      · exact (hfirst.trans ha).trans (S.reach_g hna)
  intro e he v hv
  rcases Finset.mem_union.mp he with he | he
  · obtain ⟨σ, hσ, he⟩ := Finset.mem_biUnion.mp he
    obtain ⟨c, -, he⟩ := Finset.mem_biUnion.mp he
    exact harm σ hσ c e he v hv
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
    have hp' := (Finset.mem_filter.mp hp).1
    simp only [Finset.mem_product, Finset.mem_univ, and_true] at hp'
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact ((hvalid _ hp'.1).1.trans (S.reach_sup (hvalid _ hp'.1).2 _)).trans
        (S.reach_gEnd _ _)
    · exact ((hvalid _ hp'.2).1.trans (S.reach_sup (hvalid _ hp'.2).2 _)).trans
        (S.reach_gEnd _ _)

/-- Times do not increase along edges when support edges decrease time by one and unary links
preserve it. -/
theorem time_le_of_reach (time : V → ℤ) (hsup : ∀ θ b, S.NF θ → time (S.sup θ b) + 1 = time θ)
    (hun : ∀ θ, S.UN θ → time (S.un θ) = time θ) {a b : V} (h : S.Reach a b) :
    time b ≤ time a := by
  induction h with
  | refl => exact le_rfl
  | tail _ hst ih =>
    rcases hst with ⟨hnf, bb, rfl⟩ | ⟨hu, rfl⟩
    · have := hsup _ bb hnf
      omega
    · have := hun _ hu
      omega

open Classical in
/-- **Lemma 5.1, the span assertion.** If support edges decrease time by one, unary links preserve
it, and group identifications preserve time, then every vertex of the witness has time at most
`time ρ` and at least `time ρ - e`: the span is at most `e`. -/
theorem witness_span (time : V → ℤ) (hsup : ∀ θ b, S.NF θ → time (S.sup θ b) + 1 = time θ)
    (hun : ∀ θ, S.UN θ → time (S.un θ) = time θ)
    (hgrp : ∀ φ φ', S.IsTerm φ → S.IsTerm φ' → S.grp φ = S.grp φ' → time φ = time φ')
    {ρ : V} {P : Finset (Pole V C)} (hvalid : ∀ σ ∈ P, S.Valid ρ σ)
    (hlink : ∀ σ ∈ P, ReflTransGen (S.Linked P) (S.rootPole ρ) σ) :
    ∀ e ∈ S.witness P, ∀ v ∈ e,
      time v ≤ time ρ ∧ time ρ ≤ time v + ∑ σ ∈ P, ∑ c, (S.pBin σ c : ℤ) := by
  classical
  have hK : ∀ e ∈ S.witness P, Crossing time e ∨ ∃ a b, e = s(a, b) ∧ time a = time b := by
    intro e he
    rcases Finset.mem_union.mp he with he | he
    · obtain ⟨σ, hσ, he⟩ := Finset.mem_biUnion.mp he
      obtain ⟨c, -, he⟩ := Finset.mem_biUnion.mp he
      rcases Finset.mem_insert.mp he with rfl | he
      · exact Or.inl ⟨_, _, rfl, hsup _ _ (hvalid σ hσ).2⟩
      · obtain ⟨a, -, hna, rfl⟩ := S.gEdges_spec c _ e he
        rcases hna with hna | hna
        · rw [S.g_of_NF hna]
          exact Or.inl ⟨_, _, rfl, hsup _ _ hna⟩
        · rw [S.g_of_UN hna]
          exact Or.inr ⟨_, _, rfl, (hun _ hna).symm⟩
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
      exact Or.inr ⟨_, _, rfl, hgrp _ _ (S.pEnd_isTerm _ _) (S.pEnd_isTerm _ _)
        (Finset.mem_filter.mp hp).2⟩
  have hcross : ((S.witness P).filter (Crossing time)).card ≤ ∑ σ ∈ P, ∑ c, S.pBin σ c := by
    have hg : (S.grpEdges P).filter (Crossing time) = ∅ := by
      refine Finset.filter_eq_empty_iff.mpr (fun e he hc => ?_)
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp he
      have ht := hgrp _ _ (S.pEnd_isTerm _ _) (S.pEnd_isTerm _ _) (Finset.mem_filter.mp hp).2
      obtain ⟨a, b, hab, hba⟩ := hc
      rcases Sym2.eq_iff.mp hab with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> omega
    unfold witness
    rw [Finset.filter_union, hg, Finset.union_empty]
    exact S.armEdges_crossing_card_le time hun P
  intro e he v hv
  refine ⟨S.time_le_of_reach time hsup hun (S.witness_reach hvalid e he v hv), ?_⟩
  have h1 := time_le_of_edgeReach time (S.witness P) hK (S.witness_connected hlink e he v hv)
  have h2 : (((S.witness P).filter (Crossing time)).card : ℤ) ≤
      ∑ σ ∈ P, ∑ c, (S.pBin σ c : ℤ) := by exact_mod_cast hcross
  linarith

end Span

/-! ## The constants of Section 5 -/

/-- (12) from the integer form: with `|C| = 5`, `ϱ₊ = 85`, `ϱ₋ = 715`, the bound
`85 e ≤ 800·5·(g - 1) + Ωg` is `e ≤ A₀(g - 1) + Ωg/ϱ₊` with `A₀ = 5(1 + ϱ₋/ϱ₊) = 4000/85`. -/
theorem polebound_of_int (e g : ℕ) (Ω : ℤ)
    (h : (85 : ℤ) * e ≤ (85 + 715) * 5 * ((g : ℤ) - 1) + Ω * g) :
    (e : ℚ) ≤ 5 * (1 + 715 / 85) * ((g : ℚ) - 1) + (Ω : ℚ) * g / 85 := by
  have h' : (85 : ℚ) * e ≤ (85 + 715) * 5 * ((g : ℚ) - 1) + (Ω : ℚ) * g := by exact_mod_cast h
  linarith

/-- **Lemma 5.1 with the constants of Section 5**: five charges, good gains `ϱ₊ = 85` (charge zero
gains even more), worst gains `-ϱ₋ = -715`. The selected `g` sources and groups satisfy (12),
`e ≤ A₀(g - 1) + Ωg/ϱ₊`, `A₀ = 4000/85 < 48`; the witness is connected at the root. -/
theorem grouped_terminal_estimate_paper [DecidableEq V] [Fintype C] (hC : Fintype.card C = 5)
    {ψ : C → V → ℤ} {Ω : ℤ} (hψ : S.IsPotential ψ 85 715)
    (hosc : ∀ φ φ' : C → V, (∀ c, S.IsTerm (φ c)) → (∀ c, S.IsTerm (φ' c)) →
      (∀ c c', S.grp (φ c) = S.grp (φ' c')) → ∑ c, (ψ c (φ c) - ψ c (φ' c)) ≤ Ω)
    {ρ : V} (hρ : S.NF ρ) :
    ∃ P : Finset (Pole V C), S.rootPole ρ ∈ P ∧ (∀ σ ∈ P, S.Valid ρ σ) ∧
      (∀ σ ∈ P, ReflTransGen (S.Linked P) (S.rootPole ρ) σ) ∧
      (∀ c, ∀ σ ∈ P, ∀ σ' ∈ P, S.pGrp σ c = S.pGrp σ' c → σ = σ') ∧
      (∀ σ ∈ P, ∀ c c', ∃ σ' ∈ P, S.pGrp σ' c' = S.pGrp σ c) ∧
      FNE.EdgeCount.ConnectedAt (S.witness P) ρ ∧
      ((∑ σ ∈ P, ∑ c, S.pBin σ c : ℕ) : ℚ) ≤
        4000 / 85 * ((P.card : ℚ) - 1) + (Ω : ℚ) * P.card / 85 := by
  have : Nonempty C := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨P, hr, hv, hl, hi, hs, hb⟩ :=
    S.grouped_terminal_estimate hψ (by norm_num) hosc hρ
  refine ⟨P, hr, hv, hl, hi, hs, S.witness_connected hl, ?_⟩
  rw [hC] at hb
  have := polebound_of_int (∑ σ ∈ P, ∑ c, S.pBin σ c) P.card Ω (by push_cast; exact hb)
  have e : (5 : ℚ) * (1 + 715 / 85) = 4000 / 85 := by norm_num
  rw [e] at this
  exact this

end GroupedSystem

end UND.Contour
