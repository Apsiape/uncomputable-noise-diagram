/-
# Lemma 8.4 (full-state discrepancies) (F3, F4)

Nodes F3 and F4 of `BLUEPRINT.md` (Part A.8), NEW (proof-route difference, F21 of `STATUS.md`).

Paper (Lemma 8.4): "For the parameters in Section 9, any two complete full-state trajectories
driven by the same noise coincide almost surely." Proof: "A flagged output is common. An
unflagged differing output requires a live `A_t(w - j e_y)` in one run for some `0 ≤ j < B`:
otherwise data and second coordinate are bottom and every helper proposal is the same UNKNOWN by
(4). Thus every discrepancy lies in a fixed finite union of planar translates of the birth field at
time `t - 1`. It also has a discrepant parent in the actual neighbourhood, since equal parents give
equal deterministic outputs. A discrepancy would therefore generate an infinite backward path in
this shifted union. Attach grouped contours … The geometric series has base below `1/64` … and
excludes every such infinite path, simultaneously at every root."

Formalization (generic in the chart data). The printed route bounds the live ordinary drivers by
the rare-birth field of Lemma 8.3; here they are bounded by the raw set `𝓜` directly: by Lemma 8.2
every live data reading is in `𝓜`, so a live `A_t(z)` (at least `h > K` checked providers with live,
hence marked, centre data) is itself in `𝓜` (**`live_marked`**). The discrepancy path is then
covered by the raw contours of Lemma 5.2 at the shifted anchors `w - j e_y`, with the proposal
neighbourhood (`bigNbr`, degree `≤ 2|N_F| ≤ κ`) and the `B` planar connectors (`conNbr`) as literal
edge labels; each contour of `f` flags covers at most `50 f` path steps with at most `101 f ≤ 512 f`
edges, and the union bound is Lemma 9.1 with `Δ_rare` and `K_rare` (**`discEv_null`**, base
`K_rare ε < 1`).
* **`proposal_of_dead`**: with every `A_t(w - j e_y)` bottom, the proposal is `(⊥, ⊥, UNKNOWN^B)`;
* **`disc_step`**: an unflagged discrepancy has a discrepant parent in the neighbourhood and a
  marked shifted anchor; **`flagged_complete`**: flagged outputs are the common replacement;
* **`exists_cover_C`** (the path argument of Lemma 5.2 with anchors and connectors);
* **`coupling_generic`** (Lemma 8.4): from Lemma 8.2, almost surely any two complete trajectories
  agree at time `0`.
-/
import UncomputableNoiseDiagram.Forget.Eliminate

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Relation
open scoped ENNReal

namespace UND.Forget

open UND.Rule UND.Sensors UND.Raw UND.Deep UND.Counting UND.Coh UND.Memory UND.Contour
open FNE.EdgeCount
open FNE (Plane box)

/- D21: `T = 500` stays opaque wherever `F_R^[T]` (the deep driver) appears in goals. -/
attribute [local irreducible] UND.Param.T

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData B τ}

/-! ## Deterministic part -/

/-- With every ordinary driver `A_t(w - j e_y)`, `j < B`, bottom, the proposal is
`(⊥, ⊥, UNKNOWN^B)` ("data and second coordinate are bottom and every helper proposal is the same
UNKNOWN by (4)"). -/
theorem proposal_of_dead (s : ℕ) (hB : 1 ≤ B) (x : PConfig CD) (w : ISite)
    (h : ∀ j : ℕ, j < B → drvA x (w - jy j) = none) :
    proposal s x w = (none, none, fun _ => Ival.both.repr) := by
  classical
  have h0 : drvA x w = none := by
    have := h 0 hB
    have e : jy 0 = (0 : ISite) := rfl
    rwa [e, sub_zero] at this
  unfold proposal
  rw [h0]
  simp only [ite_self, Prod.mk.injEq, true_and]
  funext j
  unfold Jf
  rw [h j.1 j.2]
  rfl

/-- **A live ordinary driver is marked** when no live reading is unmarked (Lemma 8.2): `h > K`
checked providers read live, hence marked, centre data, in two clusters. -/
theorem live_marked {ω : PNoise CD} {Y : ℤ → PConfig CD}
    (hno : ∀ t w a, ¬ UL CD Y (marked (flagE ω)) t w a) {t : ℤ} {z : ISite}
    {a : LiveLetter CD.toWangRel} (hA : drvA (Y (t - 1)) z = some a) : marked (flagE ω) t z := by
  classical
  rw [drvA, FR_eq_some_iff] at hA
  set S := Finset.univ.filter fun π : Prov =>
    chk CD.toWangRel (fun v => dataOf (Y (t - 1)) (v, z.2 + provOff π)) z.1 = some a with hS
  have hQ : UND.Param.h ≤ S.card := hA
  have hm : ∀ π ∈ S, MarkedAt (marked (flagE ω) (t - 1)) z π := by
    intro π hπ
    have c1 := (Finset.mem_filter.mp hπ).2
    simp only [chk] at c1
    split_ifs at c1 with k1
    refine ⟨0, by simp [box], ?_⟩
    by_contra hnm
    exact hno (t - 1) (z.1 + 0, z.2 + provOff π) a ⟨hnm, Or.inl (by rw [add_zero]; exact c1)⟩
  obtain ⟨π, hπ, π', hπ', hne⟩ := exists_two_clusters S (by
    have : UND.Param.h = 4 * UND.Param.K := rfl
    have hK0 : 0 < UND.Param.K := by norm_num [UND.Param.K]
    omega)
  exact marked_closed (flagE ω) t z (Or.inr ⟨π, π', hne, hm π hπ, hm π' hπ'⟩)

/-- **One discrepancy step** (Lemma 8.4): an unflagged discrepancy between two flagged trajectories
without unmarked live readings has a discrepant parent in the proposal neighbourhood and a marked
shifted anchor `w - j e_y`, `j < B`. -/
theorem disc_step (hB : 1 ≤ B) {s : ℕ} {ω : PNoise CD} {X Y : ℤ → PConfig CD}
    (hFX : IsFlagTraj CD s X (flagE ω)) (hFY : IsFlagTraj CD s Y (flagE ω))
    (hnoX : ∀ t w a, ¬ UL CD X (marked (flagE ω)) t w a)
    (hnoY : ∀ t w a, ¬ UL CD Y (marked (flagE ω)) t w a)
    {t : ℤ} {w : ISite} (hE : ¬ flagE ω t w) (hne : X t w ≠ Y t w) :
    (∃ z ∈ nbhdP B, X (t - 1) (w + z) ≠ Y (t - 1) (w + z)) ∧
      ∃ j : ℕ, j < B ∧ marked (flagE ω) t (w - jy j) := by
  have hX := hFX t w hE
  have hY := hFY t w hE
  refine ⟨?_, ?_⟩
  · by_contra hall
    push Not at hall
    exact hne (by rw [hX, hY]; exact proposal_local s hB hall)
  · by_contra hall
    push Not at hall
    have hdX : ∀ j : ℕ, j < B → drvA (X (t - 1)) (w - jy j) = none := by
      intro j hj
      cases h : drvA (X (t - 1)) (w - jy j) with
      | none => rfl
      | some a => exact absurd (live_marked hnoX h) (hall j hj)
    have hdY : ∀ j : ℕ, j < B → drvA (Y (t - 1)) (w - jy j) = none := by
      intro j hj
      cases h : drvA (Y (t - 1)) (w - jy j) with
      | none => rfl
      | some a => exact absurd (live_marked hnoY h) (hall j hj)
    exact hne (by rw [hX, hY, proposal_of_dead s hB _ w hdX, proposal_of_dead s hB _ w hdY])

/-- **Flagged outputs are the common replacement** in every complete trajectory. -/
theorem flagged_complete (CD : ChartData B τ) (s : ℕ) (hB : 1 ≤ B)
    {ω : (ruleCA CD s).Noise₂} {X : ℤ → (ruleCA CD s).Config}
    (hX : (ruleCA CD s).IsComplete ω X) (t : ℤ) (w : ISite) (hE : flagsOf ω t w) :
    decodeConfig (X t) w = decodeSym (ω (t, siteEquiv.symm w)).2 := by
  have h := hX (t - 1)
  rw [sub_add_cancel] at h
  have key := congrFun (update_decode (proposal (CD := CD) s) (nbhdP B)
    (fun x a => proposal_translate s x a) (fun _ _ _ hh => proposal_local s hB hh)
    (fun v => ω (t, v)) (X (t - 1))) w
  show decodeConfig (X t) w = _
  rw [h]
  refine key.trans ?_
  exact ite_eq_left hE

/-! ## The coupling graph and the path argument -/

/-- The proposal neighbourhood as space-time steps, both directions. -/
def bigNbr (B : ℕ) (x : Pt) : Finset Pt :=
  (nbhdP B).image (fun z => (x.1 + z, x.2 - 1)) ∪ (nbhdP B).image (fun z => (x.1 - z, x.2 + 1))

/-- The `B` planar connectors `± j e_y`, `j < B`. -/
def conNbr (B : ℕ) (x : Pt) : Finset Pt :=
  (Finset.range B).image (fun j => (x.1 - jy j, x.2)) ∪
    (Finset.range B).image (fun j => (x.1 + jy j, x.2))

/-- The coupling graph: ordinary steps, the proposal neighbourhood, the connectors. -/
def nbC (B : ℕ) (x : Pt) : Finset Pt := nbr x ∪ bigNbr B x ∪ conNbr B x

theorem card_nbC_le (B : ℕ) (x : Pt) :
    (nbC B x).card ≤ 18 * UND.Param.q + 2 * (nbhdP B).card + 2 * B := by
  have h1 := card_nbr_le x
  have h2 : (bigNbr B x).card ≤ 2 * (nbhdP B).card := by
    unfold bigNbr
    refine (Finset.card_union_le _ _).trans ?_
    have := Finset.card_image_le (s := nbhdP B) (f := fun z => (x.1 + z, x.2 - 1))
    have := Finset.card_image_le (s := nbhdP B) (f := fun z => (x.1 - z, x.2 + 1))
    omega
  have h3 : (conNbr B x).card ≤ 2 * B := by
    unfold conNbr
    refine (Finset.card_union_le _ _).trans ?_
    have := Finset.card_image_le (s := Finset.range B) (f := fun j => (x.1 - jy j, x.2))
    have := Finset.card_image_le (s := Finset.range B) (f := fun j => (x.1 + jy j, x.2))
    rw [Finset.card_range] at *
    omega
  unfold nbC
  refine (Finset.card_union_le _ _).trans ?_
  have := Finset.card_union_le (nbr x) (bigNbr B x)
  omega

theorem par_chi (x : Pt) (π : Prov) (μ : Plane) : par (chi x π μ) π μ = x := by
  obtain ⟨⟨u, P⟩, t⟩ := x
  simp [chi, par]

theorem nbr_symm {a b : Pt} (h : b ∈ nbr a) : a ∈ nbr b := by
  unfold nbr at h ⊢
  rcases Finset.mem_union.mp h with h | h
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, chi_par a p.2 p.1⟩)
  · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
    exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨p, hp, par_chi a p.2 p.1⟩)

theorem nbC_symm {a b : Pt} (h : b ∈ nbC B a) : a ∈ nbC B b := by
  unfold nbC at h ⊢
  rcases Finset.mem_union.mp h with h | h
  · rcases Finset.mem_union.mp h with h | h
    · exact Finset.mem_union_left _ (Finset.mem_union_left _ (nbr_symm h))
    · refine Finset.mem_union_left _ (Finset.mem_union_right _ ?_)
      unfold bigNbr at h ⊢
      rcases Finset.mem_union.mp h with h | h
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
        exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨z, hz, by simp⟩)
      · obtain ⟨z, hz, rfl⟩ := Finset.mem_image.mp h
        exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨z, hz, by simp⟩)
  · refine Finset.mem_union_right _ ?_
    unfold conNbr at h ⊢
    rcases Finset.mem_union.mp h with h | h
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, hj, by simp⟩)
    · obtain ⟨j, hj, rfl⟩ := Finset.mem_image.mp h
      exact Finset.mem_union_left _ (Finset.mem_image.mpr ⟨j, hj, by simp⟩)

theorem nbr_sub_nbC (x : Pt) : nbr x ⊆ nbC B x := fun _ h =>
  Finset.mem_union_left _ (Finset.mem_union_left _ h)

/-- The connector edge from a path vertex to its anchor (empty if they coincide). -/
def conEdge (q a : Pt) : Finset (Sym2 Pt) := if a = q then ∅ else {s(q, a)}

theorem conEdge_card (q a : Pt) : (conEdge q a).card ≤ 1 := by
  unfold conEdge; split_ifs <;> simp

theorem conEdge_reach (q a : Pt) : Reach (conEdge q a) q a := by
  unfold conEdge
  split_ifs with h
  · rw [h]
    exact ReflTransGen.refl
  · exact ReflTransGen.single (Finset.mem_singleton_self _)

theorem conEdge_connected (q a : Pt) : ConnectedAt (conEdge q a) q := by
  intro d hd v hv
  unfold conEdge at hd
  split_ifs at hd with h
  · simp at hd
  · rw [Finset.mem_singleton.mp hd] at hv
    rcases Sym2.mem_iff.mp hv with rfl | rfl
    · exact ReflTransGen.refl
    · exact conEdge_reach _ _ |>.trans ReflTransGen.refl

theorem conEdge_inGraph {q a : Pt} (h : a ∈ nbC B q) : InGraph (nbC B) (conEdge q a) := by
  intro x y hxy
  unfold conEdge at hxy
  split_ifs at hxy
  · simp at hxy
  · rcases Sym2.eq_iff.mp (Finset.mem_singleton.mp hxy) with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact h
    · exact nbC_symm h

theorem pathEdges_inGraphC {Q : ℕ → Pt} (hstep : ∀ k, Q (k + 1) ∈ nbC B (Q k)) (k n : ℕ) :
    InGraph (nbC B) (pathEdges Q k n) := by
  intro a b hab
  obtain ⟨i, -, he⟩ := Finset.mem_image.mp hab
  rcases Sym2.eq_iff.mp he.symm with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact hstep (k + i)
  · exact nbC_symm (hstep (k + i))

theorem inGraph_unionC {K L : Finset (Sym2 Pt)} (hK : InGraph (nbC B) K)
    (hL : InGraph (nbC B) L) : InGraph (nbC B) (K ∪ L) := by
  intro a b h
  rcases Finset.mem_union.mp h with h | h
  · exact hK a b h
  · exact hL a b h

theorem inGraph_nbr_C {K : Finset (Sym2 Pt)} (hK : InGraph nbr K) : InGraph (nbC B) K :=
  fun a b h => nbr_sub_nbC a (hK a b h)

/-- **The path argument with anchors** (Lemma 5.2's cover, for Lemma 8.4): along an infinite
backward path `Q` of coupling-graph steps whose anchors (same time, adjacent) lie in `𝓜`, for
every `m` and every start `k` there are `f ≥ 1` distinct flags, no later than `Q k`, with
`m ≤ 50 f`, and at most `101 f` coupling-graph edges connected at `Q k` containing them. -/
theorem exists_cover_C {E : ℤ → ISite → Prop} {Q : ℕ → Pt}
    (htime : ∀ k, (Q (k + 1)).2 = (Q k).2 - 1) (hstep : ∀ k, Q (k + 1) ∈ nbC B (Q k))
    (anc : ℕ → Pt) (hanc : ∀ k, (anc k).2 = (Q k).2 ∧ anc k ∈ nbC B (Q k))
    (hmark : ∀ k, marked E (anc k).2 (anc k).1) :
    ∀ m k, ∃ Fl : Finset Pt, ∃ K : Finset (Sym2 Pt), 1 ≤ Fl.card ∧ m ≤ 50 * Fl.card ∧
      K.card ≤ 101 * Fl.card ∧ ConnectedAt K (Q k) ∧ InGraph (nbC B) K ∧
      (∀ y ∈ Fl, E y.2 y.1) ∧ (∀ y ∈ Fl, y.2 ≤ (Q k).2) ∧
      (∀ y ∈ Fl, y = Q k ∨ ∃ d ∈ K, y ∈ d) := by
  classical
  have htj : ∀ k j, (Q (k + j)).2 = (Q k).2 - j := by
    intro k j
    induction j with
    | zero => simp
    | succ j ih => rw [← add_assoc, htime, ih]; push_cast; ring
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
  intro k
  obtain ⟨e, Fl₀, K₀, h1, h2, h3, h4, h5, h6, h7, h8⟩ := exists_contour (hmark k)
  have hak := hanc k
  have hC1 := conEdge_card (Q k) (anc k)
  set C₀ := conEdge (Q k) (anc k) with hC₀
  have hcon : ConnectedAt (C₀ ∪ K₀) (Q k) :=
    connectedAt_union (conEdge_connected _ _) h5
      (GroupedSystem.reach_mono Finset.subset_union_left (conEdge_reach _ _))
  have hflag₀ : ∀ y ∈ Fl₀, y = Q k ∨ ∃ d ∈ C₀ ∪ K₀, y ∈ d := by
    intro y hy
    rcases h8 y hy with rfl | ⟨d, hd, hyd⟩
    · by_cases hq : anc k = Q k
      · exact Or.inl hq
      · refine Or.inr ⟨s(Q k, anc k), Finset.mem_union_left _ ?_, Sym2.mem_mk_right _ _⟩
        simp [hC₀, conEdge, hq]
    · exact Or.inr ⟨d, Finset.mem_union_right _ hd, hyd⟩
  have hG₀ : InGraph (nbC B) (C₀ ∪ K₀) := inGraph_unionC (conEdge_inGraph hak.2) (inGraph_nbr_C h7)
  have hcardC : (C₀ ∪ K₀).card ≤ e + 1 := (Finset.card_union_le _ _).trans (by omega)
  have he48 : 2 * e + 2 ≤ 101 * Fl₀.card := by omega
  by_cases hm : m ≤ 50 * Fl₀.card
  · refine ⟨Fl₀, C₀ ∪ K₀, h1, hm, by omega, hcon, hG₀, h3, fun y hy => ?_, hflag₀⟩
    have := (h4 y hy).2
    rw [hak.1] at this
    exact this
  · obtain ⟨Fl', K', g1, g2, g3, g4, g5, g6, g7, g8⟩ :=
      ih (m - (e + 1)) (by omega) (k + (e + 1))
    have ht' := htj k (e + 1)
    have hdisj : Disjoint Fl₀ Fl' := by
      rw [Finset.disjoint_left]
      intro y hy hy'
      have a1 := (h4 y hy).1
      have a2 := g7 y hy'
      rw [hak.1] at a1
      push_cast at ht'
      omega
    have hcard : (Fl₀ ∪ Fl').card = Fl₀.card + Fl'.card := Finset.card_union_of_disjoint hdisj
    have hpath := card_pathEdges_le Q k (e + 1)
    refine ⟨Fl₀ ∪ Fl', (C₀ ∪ K₀) ∪ pathEdges Q k (e + 1) ∪ K', ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hcard]; omega
    · rw [hcard]; omega
    · rw [hcard]
      refine (Finset.card_union_le _ _).trans ?_
      have := Finset.card_union_le (C₀ ∪ K₀) (pathEdges Q k (e + 1))
      omega
    · refine connectedAt_union (connectedAt_union hcon (pathEdges_connected Q k (e + 1))
        ReflTransGen.refl) g4 ?_
      exact GroupedSystem.reach_mono (Finset.subset_union_right.trans Finset.subset_union_left)
        (pathEdges_reach Q k (e + 1) (e + 1) le_rfl)
    · exact inGraph_unionC (inGraph_unionC hG₀ (pathEdges_inGraphC hstep k (e + 1))) g5
    · intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · exact h3 y hy
      · exact g6 y hy
    · intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · have := (h4 y hy).2
        rw [hak.1] at this
        exact this
      · have := g7 y hy
        push_cast at ht'
        omega
    · intro y hy
      rcases Finset.mem_union.mp hy with hy | hy
      · rcases hflag₀ y hy with h | ⟨d, hd, hyd⟩
        · exact Or.inl h
        · exact Or.inr ⟨d, Finset.mem_union_left _ (Finset.mem_union_left _ hd), hyd⟩
      · rcases g8 y hy with h | ⟨d, hd, hyd⟩
        · refine Or.inr ⟨s(Q (k + e), Q (k + e + 1)), Finset.mem_union_left _
            (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨e, Finset.mem_range.mpr (by omega),
              rfl⟩)), ?_⟩
          rw [h, show k + (e + 1) = k + e + 1 by ring]
          exact Sym2.mem_mk_right _ _
        · exact Or.inr ⟨d, Finset.mem_union_right _ hd, hyd⟩

/-! ## The union bound -/

/-- The event of an infinite backward discrepancy-shaped path from `(w, t)`: steps in the proposal
neighbourhood, each vertex with a marked shifted anchor `p_k - j e_y`, `j < B`. -/
def DiscEv (B : ℕ) (A : UND.CA 6) (w : ISite) (t : ℤ) : Set A.Noise₂ :=
  {ω | ∃ p : ℕ → ISite, p 0 = w ∧ (∀ k, p (k + 1) - p k ∈ nbhdP B) ∧
    ∀ k : ℕ, ∃ j : ℕ, j < B ∧ marked (flagsOf ω) (t - k) (p k - jy j)}

theorem degree_le_rare (B : ℕ) (hB : 1 ≤ B) (x : Pt) :
    (nbC B x).card ≤ UND.Param.DeltaRareOf B := by
  refine (card_nbC_le B x).trans ?_
  have h1 := (card_nbhdP_le B).2
  unfold UND.Param.DeltaRareOf UND.Param.kappa
  have e : 2 * B * (UND.Param.nA + UND.Param.nQ + 2) =
      2 * (B * (UND.Param.nA + UND.Param.nQ + 2)) := by ring
  have e6 : (10 : ℕ) ^ 6 = 1000000 := by norm_num
  rw [e, e6]
  generalize B * (UND.Param.nA + UND.Param.nQ + 2) = Y at h1 ⊢
  omega

/-- **One root of Lemma 8.4**: if `K_rare ε < 1`, an infinite discrepancy-shaped path from a given
root has probability zero. -/
theorem discEv_null (A : UND.CA 6) (hB : 1 ≤ B) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (hK : (UND.Param.KrareOf B : ℝ) * ε < 1) (w : ISite) (t : ℤ) :
    A.noiseLaw₂ ε (DiscEv B A w t) = 0 := by
  classical
  set r : ℝ≥0∞ := (UND.Param.KrareOf B : ℝ≥0∞) * ENNReal.ofReal ε with hr
  have hr1 : r < 1 := by
    rw [hr, ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (Nat.cast_nonneg _)]
    exact ENNReal.ofReal_lt_one.mpr hK
  have hΔ1 : 1 ≤ UND.Param.DeltaRareOf B := UND.Param.DeltaRareOf_pos B
  have hbound : ∀ G, 1 ≤ G → A.noiseLaw₂ ε (DiscEv B A w t) ≤ ∑' j : ℕ, r ^ (j + G) := by
    intro G hG
    refine measure_le_tsum_from (A.noiseLaw₂ ε) (nbC B) (UND.Param.DeltaRareOf B) 512
      (UND.Param.KrareOf B) (degree_le_rare B hB) hΔ1
      (fun g hg => UND.Counting.four_le_KrareOf_pow B le_rfl g hg) ((w, t) : Pt) G hG
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
      choose jf hjf hmf using hmark
      let Q : ℕ → Pt := fun k => (p k, t - (k : ℤ))
      have htime : ∀ k, (Q (k + 1)).2 = (Q k).2 - 1 := fun k => by
        show t - ((k + 1 : ℕ) : ℤ) = t - (k : ℤ) - 1
        push_cast; ring
      have hstepQ : ∀ k, Q (k + 1) ∈ nbC B (Q k) := by
        intro k
        refine Finset.mem_union_left _ (Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨p (k + 1) - p k, hstep k, ?_⟩)))
        show (p k + (p (k + 1) - p k), t - (k : ℤ) - 1) = (p (k + 1), t - ((k + 1 : ℕ) : ℤ))
        refine Prod.ext (by abel) ?_
        push_cast; ring
      let anc : ℕ → Pt := fun k => (p k - jy (jf k), t - (k : ℤ))
      have hanc : ∀ k, (anc k).2 = (Q k).2 ∧ anc k ∈ nbC B (Q k) := fun k =>
        ⟨rfl, Finset.mem_union_right _ (Finset.mem_union_left _
          (Finset.mem_image.mpr ⟨jf k, Finset.mem_range.mpr (hjf k), rfl⟩))⟩
      obtain ⟨Fl, K, h1, h2, h3, h4, h5, h6, -, h8⟩ :=
        exists_cover_C (E := flagsOf ω) htime hstepQ anc hanc (fun k => hmf k) (50 * G) 0
      have hQ0 : Q 0 = (w, t) := by simp [Q, hp0]
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

/-! ## Lemma 8.4 -/

/-- **Lemma 8.4** (full-state discrepancies), generic in the chart data: if `K_rare ε < 1` and
almost surely no complete trajectory has an unmarked live reading (Lemma 8.2), then almost surely
any two complete trajectories driven by the same noise agree at time `0`. -/
theorem coupling_generic (hB : 1 ≤ B) (s : ℕ) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (hK : (UND.Param.KrareOf B : ℝ) * ε < 1)
    (hno : ∀ᵐ ω ∂((ruleCA CD s).noiseLaw₂ ε), ∀ X : ℤ → (ruleCA CD s).Config,
      (ruleCA CD s).IsComplete ω X → ∀ t w a,
        ¬ UL CD (fun t => decodeConfig (X t)) (marked (flagsOf (A := ruleCA CD s) ω)) t w a) :
    ∀ᵐ ω ∂((ruleCA CD s).noiseLaw₂ ε), ∀ X Y : ℤ → (ruleCA CD s).Config,
      (ruleCA CD s).IsComplete ω X → (ruleCA CD s).IsComplete ω Y → X 0 = Y 0 := by
  have hdisc : ∀ᵐ ω ∂((ruleCA CD s).noiseLaw₂ ε), ∀ z : ISite × ℤ,
      ω ∉ DiscEv B (ruleCA CD s) z.1 z.2 := by
    rw [ae_iff]
    refine measure_mono_null (fun ω hω => ?_)
      (measure_iUnion_null fun z : ISite × ℤ => discEv_null (ruleCA CD s) hB h0 h1 hK z.1 z.2)
    simp only [Set.mem_ofPred_eq, not_forall, not_not] at hω
    obtain ⟨z, hz⟩ := hω
    exact Set.mem_iUnion.mpr ⟨z, hz⟩
  filter_upwards [hno, hdisc] with ω hω hd
  intro X Y hX hY
  by_contra hne
  obtain ⟨w6, hw6⟩ := Function.ne_iff.mp hne
  have hFX := isFlagTraj_of_complete CD s hB hX
  have hFY := isFlagTraj_of_complete CD s hB hY
  have hnoX := hω X hX
  have hnoY := hω Y hY
  have hstep : ∀ (t : ℤ) (w : ISite), decodeConfig (X t) w ≠ decodeConfig (Y t) w →
      (∃ z ∈ nbhdP B, decodeConfig (X (t - 1)) (w + z) ≠ decodeConfig (Y (t - 1)) (w + z)) ∧
        ∃ j : ℕ, j < B ∧ marked (flagsOf (A := ruleCA CD s) ω) t (w - jy j) := by
    intro t w hne'
    have hE : ¬ flagsOf (A := ruleCA CD s) ω t w := by
      intro hE
      exact hne' ((flagged_complete CD s hB hX t w hE).trans
        (flagged_complete CD s hB hY t w hE).symm)
    exact disc_step (ω := ω) hB hFX hFY hnoX hnoY hE hne'
  choose! zf hzf hzne using fun t w h => (hstep t w h).1
  choose! jf hjf hjm using fun t w h => (hstep t w h).2
  let p : ℕ → ISite := fun k => Nat.rec (motive := fun _ => ISite) (siteEquiv w6)
    (fun k w => w + zf (0 - (k : ℤ)) w) k
  have hinv : ∀ k : ℕ, decodeConfig (X (0 - (k : ℤ))) (p k) ≠
      decodeConfig (Y (0 - (k : ℤ))) (p k) := by
    intro k
    induction k with
    | zero =>
      intro h
      apply hw6
      have h' : decodeConfig (X 0) (siteEquiv w6) = decodeConfig (Y 0) (siteEquiv w6) := by
        simpa [p] using h
      simp only [decodeConfig, AddEquiv.symm_apply_apply] at h'
      exact (Fintype.equivFin _).symm.injective h'
    | succ k ih =>
      have := hzne _ _ ih
      rwa [show (0 : ℤ) - (k : ℤ) - 1 = 0 - ((k + 1 : ℕ) : ℤ) by push_cast; ring] at this
  refine hd (siteEquiv w6, 0) ⟨p, rfl, fun k => ?_, fun k => ⟨jf _ (p k), hjf _ _ (hinv k),
    hjm _ _ (hinv k)⟩⟩
  show p k + zf (0 - (k : ℤ)) (p k) - p k ∈ nbhdP B
  rw [add_sub_cancel_left]
  exact hzf _ _ (hinv k)

end UND.Forget
