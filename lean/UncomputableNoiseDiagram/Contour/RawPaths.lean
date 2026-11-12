/-
# Lemma 5.2 (raw paths) (C2)

Node C2 of `BLUEPRINT.md` (Part A.5). NEW: the first concrete instance of Lemma 5.1
(`Contour/Grouped.lean`), on the marked derivation of `𝓜^{t₀}`, with Lemma 9.1's union bound
(`Contour/Counting.lean`).

Paper (Lemma 5.2): "For the threshold in Section 9, almost surely no infinite backward ordinary
dependency path is contained in `𝓜`. The assertion holds simultaneously at every root."
Proof: "A marked point has a contour by Lemma 5.1, with `f` distinct flags, at most `50(f-1)` arm
edges and span at most that number. A terminal root has `f = 1`, `e = 0`. Along a marked path
attach a witness at its current root and restart one step before its earliest terminal. Selected
time slabs are disjoint, so their flags are distinct. At most `50(f-1)+1 ≤ 50f` path steps are
covered by a witness; together its support and path edges cost at most `101f` edges. The graph has
fixed degree at most the `Δ` of Section 9. A doubled-edge traversal and a terminal subset encode at
most `K_mem^f` choices by Lemma 9.1. Their probability is `ε^f`. A path of length `n` forces
`f ≥ n/50`, and the geometric tail tends to zero. Countability handles all roots."

Formalization.
* Space-time points `Pt = ISite × ℤ`; an ordinary backward step (`OrdStep`, `par`) goes from
  `((u, P), t)` to `((u + μ, P + s), t - 1)` with `μ ∈ Mo`, `s` a provider vector (the data
  checker's dependency); the graph `nbr` of these steps, both directions, has degree
  `≤ 18q ≤ Δ` (`card_nbr_le`).
* The marked derivation of `𝓜^{t₀}` as a `GroupedSystem` (`sys E t₀`): vertices are space-time
  points, `rk = t - t₀`; a marked non-flag point is binary, with two marked parents in distinct
  provider clusters (`pd`, chosen by `Classical.epsilon`); for charge `c` the good parent is one
  whose cluster is not `c` (charge zero = cluster `none` = `S₀`: a nonzero cluster; charge `i`: a
  cluster other than `i`); no unary links; terminal leaves are the flags, singleton groups
  (`grp = id`); potentials (11) (`psi`, `isPotential_psi`: good gains `≥ 85`, worst `-715`).
* **`exists_contour`** (Lemma 5.2, first sentence): every point of `𝓜` has a contour
  (`IsContour`): `f ≥ 1` distinct flags, `e` positive support edges with `85 e ≤ 4000(f - 1)`
  (so `e ≤ 48(f - 1) ≤ 50(f - 1)`), flags in the time slab `[t - e, t]` (`witness_span`), and
  at most `e` ordinary-step edges connected at the root and containing every flag.
* **`exists_cover`** (the path argument): along an infinite marked ordinary path, for every `m`
  there are `f ≥ 1` distinct flags with `m ≤ 50 f` and at most `101 f` ordinary-step edges
  connected at the root containing them (witnesses with restarts one step below their slabs).
* **`raw_paths`** (Lemma 5.2): if `0 ≤ ε ≤ 1` and `K_mem ε < 1`, then almost surely, for every
  root, no infinite backward ordinary dependency path lies in `𝓜`; **`raw_paths_threshold`**:
  the same for `0 ≤ ε ≤ ε_*` (Section 9's threshold, `raw_base_lt`).
-/
import UncomputableNoiseDiagram.Contour.Coherence
import UncomputableNoiseDiagram.Contour.Counting
import UncomputableNoiseDiagram.Parameters.Bases

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Relation
open scoped ENNReal

namespace UND.Raw

open UND.Rule UND.Coh UND.Contour FNE.EdgeCount
open FNE (Plane box)

/-! ## Space-time points and ordinary steps -/

/-- Space-time points `((u, P), t)`. -/
abbrev Pt := ISite × ℤ

/-- The ordinary (data-checker) parent of `x` through the provider `π` at the planar displacement
`μ`: `((u + μ, P + s_π), t - 1)`. -/
def par (x : Pt) (π : Prov) (μ : Plane) : Pt := ((x.1.1 + μ, x.1.2 + provOff π), x.2 - 1)

/-- The inverse of `par`. -/
def chi (x : Pt) (π : Prov) (μ : Plane) : Pt := ((x.1.1 - μ, x.1.2 - provOff π), x.2 + 1)

theorem chi_par (x : Pt) (π : Prov) (μ : Plane) : chi (par x π μ) π μ = x := by
  obtain ⟨⟨u, P⟩, t⟩ := x
  simp [chi, par]

theorem par_time (x : Pt) (π : Prov) (μ : Plane) : (par x π μ).2 = x.2 - 1 := rfl

theorem par_ne (x : Pt) (π : Prov) (μ : Plane) : par x π μ ≠ x := by
  intro h
  have := congrArg Prod.snd h
  rw [par_time] at this
  omega

/-- One backward ordinary dependency step `w ↦ w'` (a Moore planar displacement and one checked
provider). -/
def OrdStep (w w' : ISite) : Prop := ∃ μ ∈ box 1, ∃ π : Prov, w' = (w.1 + μ, w.2 + provOff π)

/-- The graph of ordinary steps, both directions. -/
def nbr (x : Pt) : Finset Pt :=
  (box 1 ×ˢ (Finset.univ : Finset Prov)).image (fun p => par x p.2 p.1) ∪
    (box 1 ×ˢ (Finset.univ : Finset Prov)).image (fun p => chi x p.2 p.1)

theorem card_box_one : (box 1).card = 9 := by
  simp [FNE.box]

/-- The graph has degree at most `18q`. -/
theorem card_nbr_le (x : Pt) : (nbr x).card ≤ 18 * UND.Param.q := by
  have h : (box 1 ×ˢ (Finset.univ : Finset Prov)).card = 9 * UND.Param.q := by
    rw [Finset.card_product, card_box_one, Finset.card_univ, card_Prov]
  calc (nbr x).card ≤ _ + _ := Finset.card_union_le _ _
    _ ≤ 9 * UND.Param.q + 9 * UND.Param.q :=
        Nat.add_le_add (Finset.card_image_le.trans h.le) (Finset.card_image_le.trans h.le)
    _ = 18 * UND.Param.q := by ring

theorem par_mem_nbr (x : Pt) (π : Prov) {μ : Plane} (hμ : μ ∈ box 1) : par x π μ ∈ nbr x :=
  Finset.mem_union_left _ (Finset.mem_image.mpr ⟨(μ, π), Finset.mem_product.mpr
    ⟨hμ, Finset.mem_univ _⟩, rfl⟩)

theorem mem_nbr_par (x : Pt) (π : Prov) {μ : Plane} (hμ : μ ∈ box 1) : x ∈ nbr (par x π μ) :=
  Finset.mem_union_right _ (Finset.mem_image.mpr ⟨(μ, π), Finset.mem_product.mpr
    ⟨hμ, Finset.mem_univ _⟩, chi_par x π μ⟩)

/-- An edge `{x, par x π μ}` lies in the graph. -/
theorem inGraph_par {x : Pt} {π : Prov} {μ : Plane} (hμ : μ ∈ box 1) :
    ∀ a b, s(a, b) = s(x, par x π μ) → b ∈ nbr a := by
  intro a b h
  rcases Sym2.eq_iff.mp h with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact par_mem_nbr _ _ hμ
  · exact mem_nbr_par _ _ hμ

theorem not_isDiag_par (x : Pt) (π : Prov) (μ : Plane) : ¬ (s(x, par x π μ)).IsDiag := by
  rw [Sym2.mk_isDiag_iff]
  exact fun h => par_ne x π μ h.symm

/-! ## The marked derivation of `𝓜^{t₀}` as a grouped support graph -/

section System

variable (E : ℤ → ISite → Prop) (t0 : ℤ)

/-- Membership in `𝓜^{t₀}` of a space-time point. -/
def MF (x : Pt) : Prop := t0 ≤ x.2 ∧ markedFrom E t0 (x.2 - t0).toNat x.1

/-- An admissible choice of two marked parents in distinct provider clusters. -/
def PGood (x : Pt) (d : (Prov × Plane) × (Prov × Plane)) : Prop :=
  d.1.1.1 ≠ d.2.1.1 ∧ d.1.2 ∈ box 1 ∧ d.2.2 ∈ box 1 ∧
    MF E t0 (par x d.1.1 d.1.2) ∧ MF E t0 (par x d.2.1 d.2.2)

/-- The chosen parents. -/
def pd (x : Pt) : (Prov × Plane) × (Prov × Plane) := Classical.epsilon (PGood E t0 x)

/-- The selected parent `b` (provider and planar displacement). -/
def sel (x : Pt) (b : Bool) : Prov × Plane := if b then (pd E t0 x).1 else (pd E t0 x).2

/-- Binary vertices: marked non-flag points. -/
def NFm (x : Pt) : Prop := MF E t0 x ∧ ¬ E x.2 x.1

variable {E t0}

theorem MF.time_lt {x : Pt} (h : MF E t0 x) : t0 < x.2 := by
  obtain ⟨h1, h2⟩ := h
  by_contra hc
  have e : (x.2 - t0).toNat = 0 := by omega
  rw [e] at h2
  exact h2

theorem mf_par {x : Pt} {m : ℕ} (hm : (x.2 - t0).toNat = m + 1) {π : Prov} {μ : Plane}
    (h : markedFrom E t0 m (x.1.1 + μ, x.1.2 + provOff π)) : MF E t0 (par x π μ) := by
  refine ⟨by rw [par_time]; omega, ?_⟩
  rw [par_time, show (x.2 - 1 - t0).toNat = m by omega]
  exact h

theorem exists_pgood {x : Pt} (h : NFm E t0 x) : ∃ d, PGood E t0 x d := by
  obtain ⟨⟨h1, h2⟩, hE⟩ := h
  have hlt := MF.time_lt ⟨h1, h2⟩
  obtain ⟨m, hm⟩ : ∃ m : ℕ, (x.2 - t0).toNat = m + 1 := ⟨(x.2 - t0).toNat - 1, by omega⟩
  rw [hm] at h2
  rcases h2 with h2 | h2
  · exact absurd (by rwa [show t0 + ((m + 1 : ℕ) : ℤ) = x.2 by omega] at h2) hE
  · obtain ⟨π, π', hne, ⟨μ, hμ, hm1⟩, ⟨μ', hμ', hm2⟩⟩ := h2
    exact ⟨((π, μ), (π', μ')), hne, hμ, hμ', mf_par hm hm1, mf_par hm hm2⟩

theorem pd_spec {x : Pt} (h : NFm E t0 x) : PGood E t0 x (pd E t0 x) :=
  Classical.epsilon_spec (exists_pgood h)

theorem sel_box {x : Pt} (h : NFm E t0 x) (b : Bool) : (sel E t0 x b).2 ∈ box 1 := by
  have := pd_spec h
  cases b
  · exact this.2.2.1
  · exact this.2.1

theorem sel_mf {x : Pt} (h : NFm E t0 x) (b : Bool) :
    MF E t0 (par x (sel E t0 x b).1 (sel E t0 x b).2) := by
  have := pd_spec h
  cases b
  · exact this.2.2.2.2
  · exact this.2.2.2.1

theorem sel_ne {x : Pt} (h : NFm E t0 x) : (sel E t0 x true).1.1 ≠ (sel E t0 x false).1.1 :=
  (pd_spec h).1

variable (E t0)

/-- **The marked derivation as a grouped support graph** (Lemma 5.1's hypotheses for Lemma 5.2):
binary vertices are the marked non-flag points with their two selected marked parents in distinct
clusters, the good parent of charge `c` is one whose cluster is not `c`, there are no unary links,
and the terminal groups are singletons (`grp = id`). -/
def sys : GroupedSystem Pt (Option (Fin 4)) Pt where
  rk x := (x.2 - t0).toNat
  NF := NFm E t0
  UN _ := False
  not_UN_of_NF _ _ h := h
  sup x b := par x (sel E t0 x b).1 (sel E t0 x b).2
  un x := x
  good c x := decide ((sel E t0 x true).1.1 ≠ c)
  grp x := x
  rk_sup x b h := by
    have := MF.time_lt h.1
    show (x.2 - 1 - t0).toNat < (x.2 - t0).toNat
    omega
  rk_un _ h := h.elim

variable {E t0}

theorem sys_sup (x : Pt) (b : Bool) :
    (sys E t0).sup x b = par x (sel E t0 x b).1 (sel E t0 x b).2 := rfl

/-- The good parent of charge `c` lies in a cluster other than `c`. -/
theorem sel_good {x : Pt} (h : NFm E t0 x) (c : Option (Fin 4)) :
    (sel E t0 x ((sys E t0).good c x)).1.1 ≠ c := by
  show (sel E t0 x (decide ((sel E t0 x true).1.1 ≠ c))).1.1 ≠ c
  by_cases hc : (sel E t0 x true).1.1 = c
  · rw [decide_eq_false (not_not.mpr hc)]
    intro h'
    exact sel_ne h (hc.trans h'.symm)
  · rw [decide_eq_true hc]
    exact hc

/-! ## The potentials (11) -/

/-- The five potentials: charge `none` is `ψ₀`, charge `some i` is `ψ_{i+1}`. -/
def psi : Option (Fin 4) → Pt → ℤ
  | none, x => UND.Param.psi0 x.1.2 x.2
  | some i, x => UND.Param.psiI i x.1.2 x.2

theorem isBlockOffset_prov (π : Prov) :
    UND.Param.IsBlockOffset (fun j => ((π.2 j : ℕ) : ℤ)) := by
  intro j
  have := (π.2 j).2
  show 0 ≤ ((π.2 j : ℕ) : ℤ) ∧ ((π.2 j : ℕ) : ℤ) ≤ 15
  constructor <;> omega

/-- (11): every gain is at least `-715`; a parent in a cluster other than `c` gains at least
`85` for charge `c`. -/
theorem psi_par (c : Option (Fin 4)) (x : Pt) (π : Prov) (μ : Plane) :
    psi c x - 715 ≤ psi c (par x π μ) ∧ (π.1 ≠ c → psi c x + 85 ≤ psi c (par x π μ)) := by
  have ho := isBlockOffset_prov π
  have e : (par x π μ).1.2 = x.1.2 + (UND.Param.clusterOffset π.1 +
      fun j => ((π.2 j : ℕ) : ℤ)) := rfl
  cases c with
  | none =>
    refine ⟨?_, fun hc => ?_⟩
    · show UND.Param.psi0 x.1.2 x.2 - 715 ≤ UND.Param.psi0 (par x π μ).1.2 (par x π μ).2
      rw [e, par_time]
      exact UND.Param.gain_zero_worst _ _ _ _ ho
    · obtain ⟨i, hi⟩ := Option.ne_none_iff_exists'.mp hc
      show UND.Param.psi0 x.1.2 x.2 + 85 ≤ UND.Param.psi0 (par x π μ).1.2 (par x π μ).2
      rw [e, par_time, hi]
      have := UND.Param.gain_zero_good x.1.2 x.2 i _ ho
      linarith
  | some i =>
    refine ⟨?_, fun hc => ?_⟩
    · show UND.Param.psiI i x.1.2 x.2 - 715 ≤ UND.Param.psiI i (par x π μ).1.2 (par x π μ).2
      rw [e, par_time]
      exact UND.Param.gain_i_worst _ _ _ _ _ ho
    · show UND.Param.psiI i x.1.2 x.2 + 85 ≤ UND.Param.psiI i (par x π μ).1.2 (par x π μ).2
      rw [e, par_time]
      exact UND.Param.gain_i_good _ _ _ _ hc _ ho

theorem isPotential_psi : (sys E t0).IsPotential psi 85 715 := by
  refine ⟨fun x => ?_, fun x c h => ?_, fun x b c _ => ?_, fun x c h => h.elim⟩
  · rw [Fintype.sum_option]
    exact UND.Param.psi_sum x.1.2 x.2
  · exact (psi_par c x _ _).2 (sel_good h c)
  · exact (psi_par c x _ _).1

end System

/-! ## Contours of marked points (Lemma 5.2, first sentence) -/

section Contour

variable {E : ℤ → ISite → Prop} {t0 : ℤ}

/-- Vertices reached from a marked point are marked. -/
theorem mf_of_reach {a b : Pt} (h : (sys E t0).Reach a b) (ha : MF E t0 a) : MF E t0 b := by
  induction h with
  | refl => exact ha
  | tail _ hst ih =>
    rcases hst with ⟨hnf, bb, rfl⟩ | ⟨hu, -⟩
    · exact sel_mf hnf bb
    · exact hu.elim

/-- A marked terminal vertex is a flag. -/
theorem flag_of_term {x : Pt} (hmf : MF E t0 x) (ht : (sys E t0).IsTerm x) : E x.2 x.1 := by
  by_contra hE
  exact ht.1 ⟨hmf, hE⟩

/-- Without unary links an arm has only binary edges. -/
theorem gLen_eq_gBin (c : Option (Fin 4)) (x : Pt) :
    (sys E t0).gLen c x = (sys E t0).gBin c x := by
  refine (sys E t0).g_induction c (P := fun x => (sys E t0).gLen c x = (sys E t0).gBin c x)
    (fun x h ih => ?_) (fun x h => ?_) x
  · rcases h with h | h
    · rw [(sys E t0).gLen_of_step c (Or.inl h), (sys E t0).gBin_of_NF c h, ih]
    · exact h.elim
  · rw [(sys E t0).gLen_of_isTerm c h, (sys E t0).gBin_of_isTerm c h]

/-- Every arm edge is an ordinary step `{x, par x π μ}` from a binary vertex. -/
theorem armEdge_spec {P : Finset (GroupedSystem.Pole Pt (Option (Fin 4)))} (hP : ∀ σ ∈ P, NFm E t0 σ.loc) :
    ∀ d ∈ (sys E t0).armEdges P, ∃ x b, NFm E t0 x ∧ d = s(x, (sys E t0).sup x b) := by
  intro d hd
  obtain ⟨σ, hσ, hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨c, -, hd⟩ := Finset.mem_biUnion.mp hd
  rcases Finset.mem_insert.mp hd with rfl | hd
  · exact ⟨σ.loc, σ.fs c, hP σ hσ, rfl⟩
  · obtain ⟨a, -, hna, rfl⟩ := (sys E t0).gEdges_spec c _ d hd
    rcases hna with hna | hna
    · exact ⟨a, _, hna, by rw [(sys E t0).g_of_NF hna]⟩
    · exact hna.elim

theorem exists_edge_of_reach {V : Type*} {K : Finset (Sym2 V)} {a b : V} (h : Reach K a b)
    (hne : a ≠ b) : ∃ d ∈ K, b ∈ d := by
  rcases h.cases_tail with rfl | ⟨c, -, hc⟩
  · exact absurd rfl hne
  · exact ⟨_, hc, Sym2.mem_mk_right _ _⟩

variable (E) in
/-- **A raw contour** at `x` (Lemma 5.2): `f = |Fl| ≥ 1` distinct flags, `e` positive support edges
with `85 e ≤ 4000 (f - 1)` (so `e ≤ 48(f - 1) ≤ 50(f - 1)`), flags in the time slab
`[t - e, t]`, and a set `K` of at most `e` ordinary-step edges connected at `x` containing every
flag other than `x`. -/
def IsContour (x : Pt) (e : ℕ) (Fl : Finset Pt) (K : Finset (Sym2 Pt)) : Prop :=
  1 ≤ Fl.card ∧ 85 * e ≤ 4000 * (Fl.card - 1) ∧ (∀ y ∈ Fl, E y.2 y.1) ∧
    (∀ y ∈ Fl, x.2 - e ≤ y.2 ∧ y.2 ≤ x.2) ∧ ConnectedAt K x ∧ K.card ≤ e ∧
    UND.Counting.InGraph nbr K ∧ (∀ y ∈ Fl, y = x ∨ ∃ d ∈ K, y ∈ d)

/-- A terminal root: `f = 1`, `e = 0`. -/
theorem isContour_flag {x : Pt} (hE : E x.2 x.1) : IsContour E x 0 {x} ∅ := by
  refine ⟨by simp, by simp, fun y hy => ?_, fun y hy => ?_, fun d hd => by simp at hd, by simp,
    fun a b h => by simp at h, fun y hy => Or.inl (Finset.mem_singleton.mp hy)⟩
  · rw [Finset.mem_singleton.mp hy]; exact hE
  · rw [Finset.mem_singleton.mp hy]; simp

/-- **Lemma 5.2, a binary root**: Lemma 5.1 on the marked derivation of `𝓜^{t₀}`. -/
theorem exists_contour_nf {x : Pt} (hx : NFm E t0 x) : ∃ e Fl K, IsContour E x e Fl K := by
  classical
  obtain ⟨P, hroot, hvalid, hlink, hinj, -, hb⟩ :=
    (sys E t0).grouped_terminal_estimate isPotential_psi (by norm_num)
      ((sys E t0).hosc_singleton (ψ := psi) (fun _ _ _ _ h => h)) (ρ := x) hx
  have hC : Fintype.card (Option (Fin 4)) = 5 := by simp
  rw [hC] at hb
  push_cast at hb
  have hPnf : ∀ σ ∈ P, NFm E t0 σ.loc := fun σ hσ => (hvalid σ hσ).2
  have hmfx : MF E t0 x := hx.1
  have hreach : ∀ σ ∈ P, ∀ c, (sys E t0).Reach x ((sys E t0).pEnd σ c) := fun σ hσ c =>
    ((hvalid σ hσ).1.trans ((sys E t0).reach_sup (hvalid σ hσ).2 _)).trans
      ((sys E t0).reach_gEnd c _)
  have hflag : ∀ σ ∈ P, ∀ c, E ((sys E t0).pEnd σ c).2 ((sys E t0).pEnd σ c).1 :=
    fun σ hσ c => flag_of_term (mf_of_reach (hreach σ hσ c) hmfx) ((sys E t0).pEnd_isTerm σ c)
  have hspan := (sys E t0).witness_span Prod.snd
    (fun θ b _ => by show θ.2 - 1 + 1 = θ.2; ring) (fun θ h => h.elim)
    (fun φ φ' _ _ h => congrArg Prod.snd h) hvalid hlink
  -- the edges: the witness without loops; they are arm edges
  have hKarm : ((sys E t0).witness P).filter (fun d => ¬ d.IsDiag) ⊆ (sys E t0).armEdges P := by
    intro d hd
    obtain ⟨hdw, hnd⟩ := Finset.mem_filter.mp hd
    rcases Finset.mem_union.mp hdw with h | h
    · exact h
    · exfalso
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
      have heq : (sys E t0).pEnd p.1.1 p.1.2 = (sys E t0).pEnd p.2.1 p.2.2 :=
        ((@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).mp hp).2
      exact hnd (by rw [heq]; exact Sym2.mk_isDiag_iff.mpr rfl)
  have harm := armEdge_spec hPnf
  -- each end lies on a non-loop arm edge
  have hendK : ∀ σ ∈ P, ∀ c, ∃ d ∈ ((sys E t0).witness P).filter (fun d => ¬ d.IsDiag),
      (sys E t0).pEnd σ c ∈ d := by
    intro σ hσ c
    have hr := ((sys E t0).pEdges_reach σ c).2
    have hne : σ.loc ≠ (sys E t0).pEnd σ c := by
      intro h
      have h1 := (sys E t0).time_le_of_reach Prod.snd
        (fun θ b _ => by show θ.2 - 1 + 1 = θ.2; ring) (fun θ h => h.elim)
        ((sys E t0).reach_gEnd c ((sys E t0).pFirst σ c))
      have h2 : ((sys E t0).pFirst σ c).2 = σ.loc.2 - 1 := rfl
      have h3 : ((sys E t0).pEnd σ c).2 = σ.loc.2 := by rw [← h]
      unfold GroupedSystem.pEnd at h3
      omega
    obtain ⟨d, hd, hmem⟩ := exists_edge_of_reach hr hne
    have hdw := (sys E t0).pEdges_subset_witness hσ c hd
    have hda : d ∈ (sys E t0).armEdges P :=
      Finset.mem_biUnion.mpr ⟨σ, hσ, Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, hd⟩⟩
    obtain ⟨y, b, hy, rfl⟩ := harm d hda
    exact ⟨_, Finset.mem_filter.mpr ⟨hdw, not_isDiag_par _ _ _⟩, hmem⟩
  have hlen : ∀ σ c, (sys E t0).pLen σ c = (sys E t0).pBin σ c := fun σ c => by
    unfold GroupedSystem.pLen GroupedSystem.pBin
    rw [gLen_eq_gBin]
  have hinjE : Set.InjOn (fun σ => (sys E t0).pEnd σ none) (P : Set (GroupedSystem.Pole Pt (Option (Fin 4)))) :=
    fun σ hσ σ' hσ' h => hinj none σ hσ σ' hσ' h
  have hcard : (P.image (fun σ => (sys E t0).pEnd σ none)).card = P.card :=
    Finset.card_image_of_injOn hinjE
  have hP1 : 1 ≤ P.card := Finset.card_pos.mpr ⟨_, hroot⟩
  refine ⟨∑ σ ∈ P, ∑ c, (sys E t0).pBin σ c, P.image (fun σ => (sys E t0).pEnd σ none),
    ((sys E t0).witness P).filter (fun d => ¬ d.IsDiag), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcard]; exact hP1
  · rw [hcard]
    have : ((∑ σ ∈ P, ∑ c, (sys E t0).pBin σ c : ℕ) : ℤ) =
        ∑ σ ∈ P, ∑ c, ((sys E t0).pBin σ c : ℤ) := by push_cast; rfl
    have hb' : (85 : ℤ) * ((∑ σ ∈ P, ∑ c, (sys E t0).pBin σ c : ℕ) : ℤ) ≤
        4000 * ((P.card : ℤ) - 1) := by rw [this]; linarith
    omega
  · intro y hy
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hy
    exact hflag σ hσ none
  · intro y hy
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨d, hd, hmem⟩ := hendK σ hσ none
    have := hspan d (Finset.mem_filter.mp hd).1 _ hmem
    push_cast
    constructor <;> linarith [this.1, this.2]
  · exact UND.Counting.connectedAt_filter_not_diag ((sys E t0).witness_connected hlink)
  · refine (Finset.card_le_card hKarm).trans (((sys E t0).armEdges_card_le P).trans ?_)
    exact le_of_eq (Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun c _ => hlen σ c)
  · intro a b hab
    obtain ⟨y, bb, hy, he⟩ := harm _ (hKarm hab)
    exact inGraph_par (sel_box hy bb) a b he
  · intro y hy
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hy
    exact Or.inr (hendK σ hσ none)

/-- **Lemma 5.2, first sentence**: every point of `𝓜` has a raw contour ("a marked point has a
contour by Lemma 5.1, with `f` distinct flags, at most `50(f-1)` arm edges and span at most that
number; a terminal root has `f = 1`, `e = 0`"). -/
theorem exists_contour {x : Pt} (hx : marked E x.2 x.1) : ∃ e Fl K, IsContour E x e Fl K := by
  by_cases hE : E x.2 x.1
  · exact ⟨0, {x}, ∅, isContour_flag hE⟩
  · obtain ⟨n, hn⟩ := hx
    have hmf : MF E (x.2 - n) x :=
      ⟨by omega, by rwa [show (x.2 - (x.2 - n)).toNat = n by omega]⟩
    exact exists_contour_nf (t0 := x.2 - n) ⟨hmf, hE⟩

end Contour

/-! ## The path argument -/

section Path

variable {E : ℤ → ISite → Prop}

/-- The path edges `{Q(k+i), Q(k+i+1)}`, `i < n`. -/
def pathEdges (Q : ℕ → Pt) (k n : ℕ) : Finset (Sym2 Pt) :=
  (Finset.range n).image (fun i => s(Q (k + i), Q (k + i + 1)))

theorem card_pathEdges_le (Q : ℕ → Pt) (k n : ℕ) : (pathEdges Q k n).card ≤ n :=
  Finset.card_image_le.trans (Finset.card_range n).le

theorem pathEdges_reach (Q : ℕ → Pt) (k n : ℕ) :
    ∀ j ≤ n, Reach (pathEdges Q k n) (Q k) (Q (k + j)) := by
  intro j
  induction j with
  | zero => intro _; exact ReflTransGen.refl
  | succ j ih =>
    intro hj
    refine (ih (by omega)).tail ?_
    exact Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr (by omega), by
      rw [show k + (j + 1) = k + j + 1 by ring]⟩

theorem pathEdges_connected (Q : ℕ → Pt) (k n : ℕ) : ConnectedAt (pathEdges Q k n) (Q k) := by
  intro d hd v hv
  obtain ⟨i, hi, rfl⟩ := Finset.mem_image.mp hd
  have hi := Finset.mem_range.mp hi
  rcases Sym2.mem_iff.mp hv with rfl | rfl
  · exact pathEdges_reach Q k n i (by omega)
  · exact pathEdges_reach Q k n (i + 1) (by omega)

theorem pathEdges_inGraph {Q : ℕ → Pt}
    (hstep : ∀ k, ∃ π, ∃ μ ∈ box 1, Q (k + 1) = par (Q k) π μ) (k n : ℕ) :
    UND.Counting.InGraph nbr (pathEdges Q k n) := by
  intro a b hab
  obtain ⟨i, -, he⟩ := Finset.mem_image.mp hab
  obtain ⟨π, μ, hμ, hq⟩ := hstep (k + i)
  rw [hq] at he
  exact inGraph_par hμ a b he.symm

theorem connectedAt_union {V : Type*} [DecidableEq V] {K L : Finset (Sym2 V)} {z z' : V}
    (hK : ConnectedAt K z) (hL : ConnectedAt L z') (hr : Reach (K ∪ L) z z') :
    ConnectedAt (K ∪ L) z := by
  intro d hd v hv
  rcases Finset.mem_union.mp hd with hd | hd
  · exact GroupedSystem.reach_mono Finset.subset_union_left (hK d hd v hv)
  · exact hr.trans (GroupedSystem.reach_mono Finset.subset_union_right (hL d hd v hv))

theorem inGraph_union {K L : Finset (Sym2 Pt)} (hK : UND.Counting.InGraph nbr K)
    (hL : UND.Counting.InGraph nbr L) : UND.Counting.InGraph nbr (K ∪ L) := by
  intro a b h
  rcases Finset.mem_union.mp h with h | h
  · exact hK a b h
  · exact hL a b h

/-- **The path argument of Lemma 5.2.** Along an infinite backward ordinary path `Q` in `𝓜`, for
every `m` and every start `k` there are `f ≥ 1` distinct flags, no later than `Q k`, with
`m ≤ 50 f`, and at most `101 f` ordinary-step edges connected at `Q k` containing them: attach a
contour at the current root and restart one step below its time slab; the slabs are disjoint, so
the flags are distinct; each contour covers at most `e + 1 ≤ 50 f` path steps and costs at most
`e + (e + 1) ≤ 101 f` edges. -/
theorem exists_cover {Q : ℕ → Pt} (hstep : ∀ k, ∃ π, ∃ μ ∈ box 1, Q (k + 1) = par (Q k) π μ)
    (hmark : ∀ k, marked E (Q k).2 (Q k).1) :
    ∀ m k, ∃ Fl : Finset Pt, ∃ K : Finset (Sym2 Pt), 1 ≤ Fl.card ∧ m ≤ 50 * Fl.card ∧
      K.card ≤ 101 * Fl.card ∧ ConnectedAt K (Q k) ∧ UND.Counting.InGraph nbr K ∧
      (∀ y ∈ Fl, E y.2 y.1) ∧ (∀ y ∈ Fl, y.2 ≤ (Q k).2) ∧
      (∀ y ∈ Fl, y = Q k ∨ ∃ d ∈ K, y ∈ d) := by
  classical
  have htime : ∀ k j, (Q (k + j)).2 = (Q k).2 - j := by
    intro k j
    induction j with
    | zero => simp
    | succ j ih =>
      obtain ⟨π, μ, -, hq⟩ := hstep (k + j)
      rw [← add_assoc, hq, par_time, ih]
      push_cast; ring
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro k
  obtain ⟨e, Fl₀, K₀, h1, h2, h3, h4, h5, h6, h7, h8⟩ := exists_contour (hmark k)
  by_cases hm : m ≤ 50 * Fl₀.card
  · exact ⟨Fl₀, K₀, h1, hm, by omega, h5, h7, h3, fun y hy => (h4 y hy).2, h8⟩
  · obtain ⟨Fl', K', g1, g2, g3, g4, g5, g6, g7, g8⟩ :=
      ih (m - (e + 1)) (by omega) (k + (e + 1))
    have ht' := htime k (e + 1)
    have hdisj : Disjoint Fl₀ Fl' := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      have a1 := (h4 y hy).1
      have a2 := g7 y hy'
      push_cast at ht'
      omega
    have hcard : (Fl₀ ∪ Fl').card = Fl₀.card + Fl'.card := Finset.card_union_of_disjoint hdisj
    have hpath := card_pathEdges_le Q k (e + 1)
    refine ⟨Fl₀ ∪ Fl', K₀ ∪ pathEdges Q k (e + 1) ∪ K', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcard]; omega
    · rw [hcard]; omega
    · rw [hcard]
      refine (Finset.card_union_le _ _).trans ?_
      have := Finset.card_union_le K₀ (pathEdges Q k (e + 1))
      omega
    · refine connectedAt_union (connectedAt_union h5 (pathEdges_connected Q k (e + 1))
        ReflTransGen.refl) g4 ?_
      exact GroupedSystem.reach_mono (Finset.subset_union_right.trans Finset.subset_union_left)
        (pathEdges_reach Q k (e + 1) (e + 1) le_rfl)
    · exact inGraph_union (inGraph_union h7 (pathEdges_inGraph hstep k (e + 1))) g5
    · intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact h3 y hy
      · exact g6 y hy
    · intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact (h4 y hy).2
      · have := g7 y hy
        push_cast at ht'
        omega
    · intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · rcases h8 y hy with h | ⟨d, hd, hyd⟩
        · exact Or.inl h
        · exact Or.inr ⟨d, Finset.mem_union_left _ (Finset.mem_union_left _ hd), hyd⟩
      · rcases g8 y hy with h | ⟨d, hd, hyd⟩
        · refine Or.inr ⟨s(Q (k + e), Q (k + e + 1)), Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, Finset.mem_range.mpr (by omega),
              rfl⟩)), ?_⟩
          rw [h, show k + (e + 1) = k + e + 1 by ring]
          exact Sym2.mem_mk_right _ _
        · exact Or.inr ⟨d, Finset.mem_union_right _ hd, hyd⟩

end Path

/-! ## The union bound (Lemma 9.1) and the geometric tail -/

section Prob

/-- `P(E = 1 on Σ) = ε^{|Σ|}` for the two-sided noise (as `UND.CA.noiseLaw_flags_eq`). -/
theorem noiseLaw₂_flags_eq {d : ℕ} (A : UND.CA d) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (Sig : Finset (ℤ × UND.Site d)) :
    A.noiseLaw₂ ε {ω | ∀ p ∈ Sig, (ω p).1 = true} = ENNReal.ofReal ε ^ Sig.card := by
  have := A.isProbabilityMeasure_noiseSite h0 h1
  have hset : {ω : A.Noise₂ | ∀ p ∈ Sig, (ω p).1 = true} =
      Set.pi (Sig : Set (ℤ × UND.Site d)) (fun _ => {b : Bool × A.Sym | b.1 = true}) := by
    ext ω
    simp
  have hpi := Measure.infinitePi_pi (fun _ : ℤ × UND.Site d => A.noiseSite ε) (s := Sig)
    (t := fun _ => {b : Bool × A.Sym | b.1 = true})
    (fun _ _ => measurable_fst (measurableSet_singleton true))
  rw [hset, UND.CA.noiseLaw₂]
  refine hpi.trans ?_
  have hone : A.noiseSite ε {b : Bool × A.Sym | b.1 = true} = ENNReal.ofReal ε := by
    have : {b : Bool × A.Sym | b.1 = true} = ({true} : Set Bool) ×ˢ Set.univ := by
      ext b
      simp
    rw [this, Measure.prod_prod, measure_univ, mul_one]
    simp [FNE.flagLaw]
  simp only [hone, Finset.prod_const]

/-- "Their probability is `ε^f`": distinct space-time points are all flagged with probability
`ε^{|S|}`. -/
theorem flags_measure (A : UND.CA 6) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1) (S : Finset Pt) :
    A.noiseLaw₂ ε {ω | ∀ y ∈ S, flagsOf ω y.2 y.1} = ENNReal.ofReal ε ^ S.card := by
  have hinj : Set.InjOn (fun y : Pt => (y.2, siteEquiv.symm y.1)) (S : Set Pt) := by
    intro y _ y' _ h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext (siteEquiv.symm.injective h.2) h.1
  have e1 : {ω : A.Noise₂ | ∀ y ∈ S, flagsOf ω y.2 y.1} =
      {ω | ∀ p ∈ S.image (fun y : Pt => (y.2, siteEquiv.symm y.1)), (ω p).1 = true} := by
    ext ω
    simp only [Set.mem_ofPred_eq, Finset.mem_image]
    constructor
    · rintro h p ⟨y, hy, rfl⟩
      exact h y hy
    · intro h y hy
      exact h _ ⟨y, hy, rfl⟩
  rw [e1, noiseLaw₂_flags_eq A h0 h1, Finset.card_image_of_injOn hinj]

/-- **Lemma 9.1 with the union bound, from `G` on**: the variant of
`UND.Counting.measure_le_tsum_groups` whose outcomes all have `g ≥ G`; then
`μ(Ev) ≤ Σ_{j ≥ 0} (K x)^{j + G}`. -/
theorem measure_le_tsum_from {Ω V : Type*} [DecidableEq V] [MeasurableSpace Ω] (μ : Measure Ω)
    (nbr : V → Finset V) (Δ c Kc : ℕ) (hΔ : ∀ a, (nbr a).card ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (hK : ∀ g, 1 ≤ g → 4 * (2 * Δ ^ 2) ^ (c * g) ≤ Kc ^ g) (z : V) (G : ℕ) (hG : 1 ≤ G)
    (E : ℕ → Finset (Sym2 V) → Finset V → Set Ω) (x : ℝ≥0∞)
    (hE : ∀ g, G ≤ g → ∀ K A, UND.Counting.IsEncoding nbr z (c * g) K A → μ (E g K A) ≤ x ^ g)
    (Ev : Set Ω)
    (hEv : ∀ ω ∈ Ev, ∃ g, G ≤ g ∧ ∃ K A, UND.Counting.IsEncoding nbr z (c * g) K A ∧
      ω ∈ E g K A) :
    μ Ev ≤ ∑' j : ℕ, ((Kc : ℝ≥0∞) * x) ^ (j + G) := by
  classical
  set F : ℕ → Set Ω := fun j => ⋃ p ∈ (UND.Counting.encLe nbr z (c * (j + G))).filter
    (fun p => UND.Counting.IsEncoding nbr z (c * (j + G)) p.1 p.2), E (j + G) p.1 p.2 with hF
  have hsub : Ev ⊆ ⋃ j, F j := by
    intro ω hω
    obtain ⟨g, hg, K, A, henc, hωE⟩ := hEv ω hω
    obtain ⟨j, rfl⟩ : ∃ j, g = j + G := ⟨g - G, by omega⟩
    refine Set.mem_iUnion.mpr ⟨j, ?_⟩
    simp only [hF, Set.mem_iUnion]
    exact ⟨(K, A), Finset.mem_filter.mpr ⟨UND.Counting.mem_encLe nbr Δ hΔ henc, henc⟩, hωE⟩
  have hFj : ∀ j, μ (F j) ≤ ((Kc : ℝ≥0∞) * x) ^ (j + G) := by
    intro j
    refine (UND.Counting.measure_biUnion_le_card_mul μ _ _ (x ^ (j + G))
      (fun p hp => hE (j + G) (by omega) p.1 p.2 (Finset.mem_filter.mp hp).2)).trans ?_
    rw [mul_pow]
    gcongr
    have h1 := (Finset.card_filter_le (UND.Counting.encLe nbr z (c * (j + G)))
      (fun p => UND.Counting.IsEncoding nbr z (c * (j + G)) p.1 p.2)).trans
      ((UND.Counting.card_encLe_le nbr Δ hΔ hΔ1 z _).trans (hK (j + G) (by omega)))
    exact_mod_cast h1
  calc μ Ev ≤ μ (⋃ j, F j) := measure_mono hsub
    _ ≤ ∑' j, μ (F j) := measure_iUnion_le _
    _ ≤ ∑' j : ℕ, ((Kc : ℝ≥0∞) * x) ^ (j + G) := ENNReal.tsum_le_tsum hFj

/-- The event of an infinite backward ordinary path in `𝓜` from the root `(w, t)`. -/
def PathEv (A : UND.CA 6) (w : ISite) (t : ℤ) : Set A.Noise₂ :=
  {ω | ∃ p : ℕ → ISite, p 0 = w ∧ (∀ k, OrdStep (p k) (p (k + 1))) ∧
    ∀ k : ℕ, marked (flagsOf ω) (t - k) (p k)}

/-- One root: the event of an infinite marked path has probability zero. -/
theorem pathEv_null (A : UND.CA 6) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (hK : (UND.Param.Kmem : ℝ) * ε < 1) (w : ISite) (t : ℤ) :
    A.noiseLaw₂ ε (PathEv A w t) = 0 := by
  set r : ℝ≥0∞ := (UND.Param.Kmem : ℝ≥0∞) * ENNReal.ofReal ε with hr
  have hr1 : r < 1 := by
    rw [hr, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_lt_one.mpr hK
  have hΔD : 18 * UND.Param.q ≤ UND.Param.Delta := by
    rw [UND.Param.Delta_eq]; norm_num [UND.Param.q, UND.Param.K]
  have hbound : ∀ G, 1 ≤ G → A.noiseLaw₂ ε (PathEv A w t) ≤ ∑' j : ℕ, r ^ (j + G) := by
    intro G hG
    refine measure_le_tsum_from (A.noiseLaw₂ ε) nbr (18 * UND.Param.q) 256 UND.Param.Kmem
      card_nbr_le (by norm_num [UND.Param.q, UND.Param.K])
      (fun g hg => UND.Counting.four_le_Kmem_pow_of_le hΔD g hg) ((w, t) : Pt) G hG
      (fun g _ Fl => {ω | Fl.card = g ∧ ∀ y ∈ Fl, flagsOf ω y.2 y.1}) (ENNReal.ofReal ε) ?_ _ ?_
    · intro g _ K Fl _
      by_cases hc : Fl.card = g
      · calc A.noiseLaw₂ ε {ω | Fl.card = g ∧ ∀ y ∈ Fl, flagsOf ω y.2 y.1}
            ≤ A.noiseLaw₂ ε {ω | ∀ y ∈ Fl, flagsOf ω y.2 y.1} :=
              measure_mono (fun ω (h : Fl.card = g ∧ ∀ y ∈ Fl, flagsOf ω y.2 y.1) => h.2)
          _ = ENNReal.ofReal ε ^ g := by rw [flags_measure A h0 h1, hc]
      · calc A.noiseLaw₂ ε {ω | Fl.card = g ∧ ∀ y ∈ Fl, flagsOf ω y.2 y.1}
            ≤ A.noiseLaw₂ ε ∅ :=
              measure_mono (fun ω (h : Fl.card = g ∧ ∀ y ∈ Fl, flagsOf ω y.2 y.1) =>
                absurd h.1 hc)
          _ ≤ ENNReal.ofReal ε ^ g := by simp
    · intro ω hω
      obtain ⟨p, hp0, hstep, hmark⟩ := hω
      have hstepQ : ∀ k, ∃ π, ∃ μ ∈ box 1, ((p (k + 1), t - ((k + 1 : ℕ) : ℤ)) : Pt) =
          par (p k, t - (k : ℤ)) π μ := by
        intro k
        obtain ⟨μ, hμ, π, he⟩ := hstep k
        refine ⟨π, μ, hμ, Prod.ext he ?_⟩
        show t - ((k + 1 : ℕ) : ℤ) = t - (k : ℤ) - 1
        push_cast; ring
      obtain ⟨Fl, K, h1, h2, h3, h4, h5, h6, -, h8⟩ :=
        exists_cover (E := flagsOf ω) (Q := fun k => (p k, t - (k : ℤ))) hstepQ
          (fun k => hmark k) (50 * G) 0
      have hQ0 : ((p 0, t - ((0 : ℕ) : ℤ)) : Pt) = (w, t) := by simp [hp0]
      rw [hQ0] at h4 h8
      refine ⟨Fl.card, by omega, K, Fl, ⟨by omega, h5, h4, h8⟩, ?_⟩
      show Fl.card = Fl.card ∧ ∀ y ∈ Fl, flagsOf ω y.2 y.1
      exact ⟨rfl, h6⟩
  have hsum : ∑' n : ℕ, r ^ n ≠ ⊤ := by
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_ne_top.mpr (tsub_pos_of_lt hr1).ne'
  have ht := (ENNReal.tendsto_sum_nat_add (fun n => r ^ n) hsum).comp
    (Filter.tendsto_add_atTop_nat 1)
  exact le_zero_iff.mp (ge_of_tendsto' ht (fun i => hbound (i + 1) (by omega)))

/-- **Lemma 5.2** (raw paths). If `0 ≤ ε ≤ 1` and `K_mem ε < 1`, then almost surely no infinite
backward ordinary dependency path is contained in `𝓜`, simultaneously at every root: for every
time `t` and every path `p` of ordinary steps, some `(p k, t - k)` is unmarked. -/
theorem raw_paths (A : UND.CA 6) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (hK : (UND.Param.Kmem : ℝ) * ε < 1) :
    ∀ᵐ ω ∂(A.noiseLaw₂ ε), ∀ (t : ℤ) (p : ℕ → ISite), (∀ k, OrdStep (p k) (p (k + 1))) →
      ¬ ∀ k : ℕ, marked (flagsOf ω) (t - k) (p k) := by
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_)
    (measure_iUnion_null (fun z : ISite × ℤ => pathEv_null A h0 h1 hK z.1 z.2))
  simp only [Set.mem_ofPred_eq] at hω
  push Not at hω
  obtain ⟨t, p, hs, hm⟩ := hω
  exact Set.mem_iUnion.mpr ⟨(p 0, t), p, rfl, hs, hm⟩

/-- **Lemma 5.2 at the threshold of Section 9**: for `0 ≤ ε ≤ ε_*` (`K_mem ε < 1/64`,
`raw_base_lt`). -/
theorem raw_paths_threshold (A : UND.CA 6) {ε : ℝ} (h0 : 0 ≤ ε)
    (hε : ε ≤ (UND.Param.epsStar : ℝ)) :
    ∀ᵐ ω ∂(A.noiseLaw₂ ε), ∀ (t : ℤ) (p : ℕ → ISite), (∀ k, OrdStep (p k) (p (k + 1))) →
      ¬ ∀ k : ℕ, marked (flagsOf ω) (t - k) (p k) := by
  have hle : ε ≤ ((((64 * UND.Param.Kmem : ℕ) : ℚ) ^ 4)⁻¹ : ℚ) :=
    hε.trans (Rat.cast_le.mpr UND.Param.epsStar_le_mem)
  have hK := UND.Param.raw_base_lt hle
  have hK1 : (1 : ℝ) ≤ UND.Param.Kmem := by exact_mod_cast UND.Param.Kmem_pos
  refine raw_paths A h0 ?_ (by linarith)
  nlinarith

end Prob

end UND.Raw
