/-
# Basic facts about the objects of the statement file

* the constant `ε₀` (`cor:eight`);
* Wang tilings and cloned tilings (`set:def-wang`, `mem:clone`);
* `mem:basic`(a): for `k ≥ 2` at most one live symbol meets the quorum, so the
  `Classical.choose` in `quorumRule` is immaterial.
-/
import FixedNoiseErgodicity.Statements

set_option autoImplicit false

noncomputable section

namespace FNE

/-! ## The constant of `cor:eight` -/

/-- `cor:eight`: `ε₀ = (4 D₀²)^(-a) = 490000^(-99)`. -/
theorem eps0_eq : eps0 = ((490000 : ℝ) ^ 99)⁻¹ := by
  unfold eps0; norm_num

theorem eps0_pos : 0 < eps0 := by
  rw [eps0_eq]; positivity

theorem eps0_lt_one : eps0 < 1 := by
  rw [eps0_eq]
  exact inv_lt_one_of_one_lt₀ (one_lt_pow₀ (by norm_num) (by norm_num))

/-! ## Wang tilings (`set:def-wang`) -/

/-- `set:def-wang`. A *tiling* by `R`: a map `ℤ² → R` that matches on every horizontal and
every vertical edge. -/
def IsTiling (R : WangSet) (z : Plane → Tile) : Prop :=
  (∀ u, z u ∈ R) ∧ (∀ u, (z u).E = (z (u + (1, 0))).W) ∧ ∀ u, (z u).N = (z (u + (0, 1))).S

/-- `set:def-wang`. `R` *tiles* if it has a tiling. -/
def Tiles (R : WangSet) : Prop := ∃ z, IsTiling R z

/-- `mem:clone`. The block `θ[u] : w ↦ θ(u + w)` of a tiling at `u`; it is legal. -/
def tilingBlock {R : WangSet} {θ : Plane → Tile} (hθ : IsTiling R θ) (u : Plane) :
    LegalBlock R :=
  ⟨fun w => ⟨θ (u + w.1), hθ.1 _⟩, by
    constructor
    · intro w w' h
      show (θ (u + w.1)).E = (θ (u + w'.1)).W
      rw [h, ← add_assoc]; exact hθ.2.1 _
    · intro w w' h
      show (θ (u + w.1)).N = (θ (u + w'.1)).S
      rw [h, ← add_assoc]; exact hθ.2.2 _⟩

/-- Section 2.1. The block configuration `ẑ(u) = (z^{[u]}, 0)` of a tiling. -/
def blockConfig {R : WangSet} {θ : Plane → Tile} (hθ : IsTiling R θ) (u : Plane) :
    LiveSymbol R :=
  (tilingBlock hθ u, false)

/-- Section 2.1: `ẑ(u + d)` is compatible with `ẑ(u)` at displacement `d`. -/
theorem blockConfig_compatible {R : WangSet} {θ : Plane → Tile} (hθ : IsTiling R θ)
    (u d : Plane) : Compatible (blockConfig hθ u) (blockConfig hθ (u + d)) d := by
  refine ⟨rfl, fun w w' hw => ?_⟩
  apply Subtype.ext
  show θ (u + w.1) = θ (u + d + w'.1)
  rw [hw]
  congr 1
  abel

/-- `mem:clone`. The cloned tiling `ξ(u, P) = (θ[u], 0)`. -/
def clonedTiling (k : ℕ) {R : WangSet} {θ : Plane → Tile} (hθ : IsTiling R θ) : Config k R :=
  fun v => .live (blockConfig hθ v.1)

/-! ## The process -/

theorem run_zero {k : ℕ} {R : WangSet} (x : Config k R) (ω : Noise k R) : run x ω 0 = x := rfl

theorem run_succ {k : ℕ} {R : WangSet} (x : Config k R) (ω : Noise k R) (t : ℕ) (v : Site k) :
    run x ω (t + 1) v =
      if (ω (t, v)).1 then (ω (t, v)).2 else quorumRule k R (run x ω t) v := rfl

/-- The checker outputs a live symbol only by keeping its centre (`set:def-checker`). -/
theorem checker_eq_live {R : WangSet} {y : Plane → Sym R} {u : Plane} {s : LiveSymbol R}
    (h : checker y u = .live s) : y u = .live s := by
  unfold checker at h
  split_ifs at h
  exact h

/-! ## `mem:basic`(a): uniqueness of the quorum symbol -/

section Quorum

variable {k : ℕ} {R : WangSet}

/-- `mem:basic`(a). For `k ≥ 2` two different symbols cannot both be read by `k` providers. -/
theorem quorum_unique (hk : 2 ≤ k) (y : Config k R) (v : Site k) {s s' : Sym R}
    (hs : k ≤ quorumCount y v s) (hs' : k ≤ quorumCount y v s') : s = s' := by
  by_contra hne
  classical
  have hdisj : Disjoint
      (Finset.univ.filter (fun i : Option (Fin k) => y (v.1, v.2 + provider k i) = s))
      (Finset.univ.filter (fun i : Option (Fin k) => y (v.1, v.2 + provider k i) = s')) := by
    rw [Finset.disjoint_filter]
    intro i _ h1 h2
    exact hne (h1.symm.trans h2)
  have hcard := Finset.card_union_of_disjoint hdisj
  have hle := Finset.card_le_univ
    ((Finset.univ.filter (fun i : Option (Fin k) => y (v.1, v.2 + provider k i) = s)) ∪
      (Finset.univ.filter (fun i : Option (Fin k) => y (v.1, v.2 + provider k i) = s')))
  simp only [Fintype.card_option, Fintype.card_fin] at hle
  unfold quorumCount at hs hs'
  omega

/-- `set:def-quorum`, read with `mem:basic`(a): for `k ≥ 2`, `F(x)(v) = s` (live) exactly when
at least `k` providers read `s`. -/
theorem quorumRule_eq_live_iff (hk : 2 ≤ k) (x : Config k R) (v : Site k) (s : LiveSymbol R) :
    quorumRule k R x v = .live s ↔ k ≤ quorumCount (checkAll x) v (.live s) := by
  unfold quorumRule
  constructor
  · intro h
    split_ifs at h with hex
    · cases h
      exact hex.choose_spec
  · intro h
    have hex : ∃ s : LiveSymbol R, k ≤ quorumCount (checkAll x) v (.live s) := ⟨s, h⟩
    rw [dif_pos hex]
    have := quorum_unique hk (checkAll x) v hex.choose_spec h
    cases this
    rfl

/-- `set:def-quorum`: the rule outputs `⊥` when no live symbol meets the quorum. -/
theorem quorumRule_eq_bot_iff (x : Config k R) (v : Site k) :
    quorumRule k R x v = .bot ↔ ∀ s : LiveSymbol R, quorumCount (checkAll x) v (.live s) < k := by
  unfold quorumRule
  constructor
  · intro h s
    by_contra hs
    push Not at hs
    rw [dif_pos ⟨s, hs⟩] at h
    cases h
  · intro h
    rw [dif_neg]
    push Not
    exact h

end Quorum

end FNE
