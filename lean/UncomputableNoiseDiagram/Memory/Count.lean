/-
# Lemma 7.2 (counting the memory witnesses), the combinatorial core (Mem3)

Node Mem3 of `BLUEPRINT.md` (Part A.7), NEW (on Lemma 5.1, `Contour/Grouped.lean`, and Lemma 9.1,
`Contour/Counting.lean`).

Paper (Lemma 7.2): "The error event at a prescribed site and time is contained in a union of at
most `K_mem^g` events for each `g ≥ 1`, each requiring `g` distinct source labels."
Proof: "… Terminal leaves with one source label have exactly equal potentials, even at unequal
physical times. Lemma 5.1 gives at most `48(g-1)` positive edges. Suppress each maximal
source-free characteristic corridor to a corridor link and its entry link. … Thus there are at
most two unary entry/corridor links per positive support edge, plus at most `5g` terminal
source-role links. The total is less than `149g < 256g`. Project the selected witness to
characteristic coordinates, bin, virtual level and finite role, and take the union of repeated
edges. It remains connected and keeps `g` distinct marked source labels. Its degree is bounded by
the `B`-independent `Δ` in Lemma 9.1 … Doubled-edge traversals and source subsets give the claimed
count there."

Formalization (abstract: any grouped derivation system whose groups are source labels):
* **`grpEdges_card_le_lin`**: when each charge's arms end in distinct groups, the group links
  number at most `|C|²|P|` (each group receives at most one arm end per charge). With five
  charges this is `25g`, used in place of the printed star count `5g`; the total stays below
  `256g` (`3·4000/85·(g-1) + 25g < 167g`). This settles the group-link count of D14(b) for
  Lemma 7.2 without a star sub-witness.
* `armEdge_step`, `grpEdge_spec` (the witness consists of system steps and same-group links);
* **`mem_contour`** (Lemma 5.1 with zero group oscillation and at most two unary links in a row):
  a copied-arm witness with `|P| = g` poles, `g` distinct groups per charge, connected at the
  root, at most `167g` edges;
* **`mem_encoding`**: at every root (binary, unary or terminal) the projected witness is a
  literal encoding (`IsEncoding`, at most `256g` edges) whose marked set carries exactly `g`
  distinct labels, each the projection of a terminal leaf reached from the root (unary prefixes
  cost one edge each, `prepend`);
* **`mem_union`** (Lemma 7.2 with Lemma 6.3): if every outcome of an event has such an encoding
  with every marked label a source (`R ∪ S`), and the joint source law gives `γ^{|G|}` for any
  `G` distinct labels, then the event has measure at most `Σ_{g ≥ 1}(K_mem γ)^g`.
-/
import UncomputableNoiseDiagram.Contour.RawPaths

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory Relation
open scoped ENNReal

namespace UND.Contour.GroupedSystem

open FNE.EdgeCount

variable {V C Γ : Type*} (S : GroupedSystem V C Γ)

theorem prop_of_mem_filter {α : Type*} {p : α → Prop} {s : Finset α} {inst : DecidablePred p}
    {a : α} (h : a ∈ @Finset.filter α p inst s) : a ∈ s ∧ p a :=
  (@Finset.mem_filter α p inst s a).mp h

/-- **Group links, linear count**: if the arms of each charge end in distinct groups, there are
at most `|C|²|P|` group links. -/
theorem grpEdges_card_le_lin [DecidableEq V] [Fintype C] (P : Finset (Pole V C))
    (hinj : ∀ c, ∀ σ ∈ P, ∀ σ' ∈ P, S.pGrp σ c = S.pGrp σ' c → σ = σ') :
    (S.grpEdges P).card ≤ Fintype.card C ^ 2 * P.card := by
  classical
  unfold grpEdges
  refine Finset.card_image_le.trans ?_
  calc _ ≤ ((P ×ˢ (Finset.univ : Finset C)) ×ˢ (Finset.univ : Finset C)).card := by
        refine Finset.card_le_card_of_injOn (fun p => (p.1, p.2.2)) ?_ ?_
        · intro p hp
          have hp' := (prop_of_mem_filter (Finset.mem_coe.1 hp)).1
          rw [Finset.mem_product] at hp'
          exact Finset.mem_coe.2 (Finset.mem_product.2 ⟨hp'.1, Finset.mem_univ _⟩)
        · intro p hp q hq hpq
          obtain ⟨hp1, hp2⟩ := prop_of_mem_filter (Finset.mem_coe.1 hp)
          obtain ⟨hq1, hq2⟩ := prop_of_mem_filter (Finset.mem_coe.1 hq)
          rw [Finset.mem_product, Finset.mem_product] at hp1 hq1
          have hpq' : (p.1, p.2.2) = (q.1, q.2.2) := hpq
          obtain ⟨h1, h2⟩ := Prod.mk.inj hpq'
          have h3 : S.pGrp p.2.1 p.2.2 = S.pGrp q.2.1 p.2.2 := by
            rw [← hp2, h1, hq2, h2]
          have h4 := hinj p.2.2 p.2.1 (Finset.mem_product.1 hp1.2).1 q.2.1
            (Finset.mem_product.1 hq1.2).1 h3
          exact Prod.ext h1 (Prod.ext h4 h2)
    _ = Fintype.card C ^ 2 * P.card := by
        simp only [Finset.card_product, Finset.card_univ]
        ring

/-- Every arm edge is a step of the system. -/
theorem armEdge_step [DecidableEq V] [Fintype C] (P : Finset (Pole V C)) (hP : ∀ σ ∈ P, S.NF σ.loc) :
    ∀ d ∈ S.armEdges P, ∃ a b, S.Step a b ∧ d = s(a, b) := by
  classical
  intro d hd
  obtain ⟨σ, hσ, hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨c, -, hd⟩ := Finset.mem_biUnion.mp hd
  rcases Finset.mem_insert.mp hd with rfl | hd
  · exact ⟨σ.loc, S.pFirst σ c, Or.inl ⟨hP σ hσ, σ.fs c, rfl⟩, rfl⟩
  · obtain ⟨a, -, hna, rfl⟩ := S.gEdges_spec c _ d hd
    refine ⟨a, S.g c a, ?_, rfl⟩
    rcases hna with hna | hna
    · exact Or.inl ⟨hna, S.good c a, S.g_of_NF hna⟩
    · exact Or.inr ⟨hna, S.g_of_UN hna⟩

/-- Every group link joins two arm ends in one group. -/
theorem grpEdge_spec [DecidableEq V] [Fintype C] (P : Finset (Pole V C)) :
    ∀ d ∈ S.grpEdges P, ∃ σ c σ' c', S.pGrp σ c = S.pGrp σ' c' ∧
      d = s(S.pEnd σ c, S.pEnd σ' c') := by
  classical
  intro d hd
  unfold grpEdges at hd
  obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hd
  exact ⟨p.1.1, p.1.2, p.2.1, p.2.2, (prop_of_mem_filter hp).2, rfl⟩

/-- **Lemma 7.2, the edge budget** (Lemma 5.1 with zero group oscillation): a copied-arm witness
with at most `167 |P|` edges. -/
theorem mem_contour [DecidableEq V] [Fintype C] (hC : Fintype.card C = 5) {ψ : C → V → ℤ}
    (hψ : S.IsPotential ψ 85 715)
    (hgrp : ∀ φ φ', S.IsTerm φ → S.IsTerm φ' → S.grp φ = S.grp φ' → ∀ c, ψ c φ = ψ c φ')
    (hUUU : ∀ θ, S.UN θ → S.UN (S.un θ) → ¬ S.UN (S.un (S.un θ))) {ρ : V} (hρ : S.NF ρ) :
    ∃ P : Finset (Pole V C), S.rootPole ρ ∈ P ∧ (∀ σ ∈ P, S.Valid ρ σ) ∧
      (∀ c, ∀ σ ∈ P, ∀ σ' ∈ P, S.pGrp σ c = S.pGrp σ' c → σ = σ') ∧
      (∀ σ ∈ P, ∀ c c', ∃ σ' ∈ P, S.pGrp σ' c' = S.pGrp σ c) ∧
      ConnectedAt (S.witness P) ρ ∧ (S.witness P).card ≤ 167 * P.card := by
  have hosc : ∀ φ φ' : C → V, (∀ c, S.IsTerm (φ c)) → (∀ c, S.IsTerm (φ' c)) →
      (∀ c c', S.grp (φ c) = S.grp (φ' c')) → ∑ c, (ψ c (φ c) - ψ c (φ' c)) ≤ 0 := by
    intro φ φ' h h' hg
    refine le_of_eq (Finset.sum_eq_zero fun c _ => ?_)
    rw [hgrp _ _ (h c) (h' c) (hg c c) c, sub_self]
  obtain ⟨P, hr, hv, -, hi, hcov, hconn, hb⟩ := S.grouped_terminal_estimate_paper hC hψ hosc hρ
  refine ⟨P, hr, hv, hi, hcov, hconn, ?_⟩
  have hlen : ∑ σ ∈ P, ∑ c, S.pLen σ c ≤ 3 * ∑ σ ∈ P, ∑ c, S.pBin σ c := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun σ _ => ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun c _ => S.pLen_le_three_pBin hUUU σ c
  have hg := S.grpEdges_card_le_lin P hi
  rw [hC] at hg
  have hw := S.witness_card_le P
  have hb' : ((∑ σ ∈ P, ∑ c, S.pBin σ c : ℕ) : ℚ) ≤ 4000 / 85 * ((P.card : ℚ) - 1) := by
    simpa using hb
  have hq : ((S.witness P).card : ℚ) ≤ 167 * P.card := by
    have h1 : ((S.witness P).card : ℚ) ≤
        3 * ((∑ σ ∈ P, ∑ c, S.pBin σ c : ℕ) : ℚ) + 25 * P.card := by
      have : (S.witness P).card ≤ 3 * ∑ σ ∈ P, ∑ c, S.pBin σ c + 25 * P.card := by
        have := hlen; have := hg; omega
      exact_mod_cast this
    have hP0 : (0 : ℚ) ≤ P.card := Nat.cast_nonneg _
    linarith
  exact_mod_cast hq

/-! ## Projected witnesses -/

theorem reach_image {W : Type*} [DecidableEq W] (f : V → W) {K : Finset (Sym2 V)} {z v : V}
    (h : FNE.EdgeCount.Reach K z v) :
    FNE.EdgeCount.Reach (K.image (Sym2.map f)) (f z) (f v) := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail b c _ hbc ih =>
    exact ih.tail (Finset.mem_image.mpr ⟨s(b, c), hbc, by simp⟩)

theorem reach_filter_not_diag [DecidableEq V] {K : Finset (Sym2 V)} {z v : V}
    (h : FNE.EdgeCount.Reach K z v) :
    FNE.EdgeCount.Reach (K.filter (fun e => ¬ e.IsDiag)) z v := by
  induction h with
  | refl => exact ReflTransGen.refl
  | @tail b c _ hbc ih =>
    by_cases hd : b = c
    · subst hd
      exact ih
    · exact ih.tail (Finset.mem_filter.mpr ⟨hbc, by simpa using hd⟩)

/-- The data of a memory encoding at a root: an edge set with at most `n` edges in the graph,
connected at the image of the root, a marked set covered by it, with exactly `g` labels, each the
image of a terminal leaf reached from the root. -/
def MemEnc {W L : Type*} [DecidableEq L] (nbr : W → Finset W) (f : V → W) (lab : W → L)
    (ρ : V) (g n : ℕ) (K : Finset (Sym2 W)) (A : Finset W) : Prop :=
  K.card ≤ n ∧ UND.Counting.InGraph nbr K ∧ ConnectedAt K (f ρ) ∧
    (∀ v ∈ A, v = f ρ ∨ ∃ e ∈ K, v ∈ e) ∧ (A.image lab).card = g ∧
    ∀ v ∈ A, ∃ φ, S.Reach ρ φ ∧ S.IsTerm φ ∧ v = f φ

/-- **A unary or binary step in front of an encoding** costs one edge. -/
theorem prepend {W L : Type*} [DecidableEq W] [DecidableEq L] (nbr : W → Finset W) (f : V → W)
    (lab : W → L)
    (hstep : ∀ a b, S.Step a b → f a ≠ f b → f b ∈ nbr (f a) ∧ f a ∈ nbr (f b))
    {a b : V} (hab : S.Step a b) {g n : ℕ} {K : Finset (Sym2 W)} {A : Finset W}
    (h : S.MemEnc nbr f lab b g n K A) :
    ∃ K', S.MemEnc nbr f lab a g (n + 1) K' A := by
  classical
  obtain ⟨hcard, hG, hconn, hcov, hlab, hterm⟩ := h
  have hreach : S.Reach a b := ReflTransGen.single hab
  have hterm' : ∀ v ∈ A, ∃ φ, S.Reach a φ ∧ S.IsTerm φ ∧ v = f φ := by
    intro v hv
    obtain ⟨φ, h1, h2, h3⟩ := hterm v hv
    exact ⟨φ, hreach.trans h1, h2, h3⟩
  by_cases hfe : f a = f b
  · refine ⟨K, hcard.trans (Nat.le_succ n), hG, hfe ▸ hconn, fun v hv => ?_, hlab, hterm'⟩
    rw [hfe]
    exact hcov v hv
  · obtain ⟨hn1, hn2⟩ := hstep a b hab hfe
    refine ⟨insert s(f a, f b) K, (Finset.card_insert_le _ _).trans (Nat.succ_le_succ hcard),
      ?_, ?_, ?_, hlab, hterm'⟩
    · intro x y hxy
      rcases Finset.mem_insert.mp hxy with he | he
      · rcases Sym2.eq_iff.mp he with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
        · exact hn1
        · exact hn2
      · exact hG x y he
    · have hab' : FNE.EdgeCount.Reach (insert s(f a, f b) K) (f a) (f b) :=
        ReflTransGen.single (Finset.mem_insert_self _ _)
      intro e he v hv
      rcases Finset.mem_insert.mp he with rfl | he
      · rcases Sym2.mem_iff.mp hv with rfl | rfl
        · exact ReflTransGen.refl
        · exact hab'
      · exact hab'.trans (UND.Contour.GroupedSystem.reach_mono (Finset.subset_insert _ _)
          (hconn e he v hv))
    · intro v hv
      rcases hcov v hv with rfl | ⟨e, he, hve⟩
      · exact Or.inr ⟨s(f a, f b), Finset.mem_insert_self _ _, Sym2.mem_mk_right _ _⟩
      · exact Or.inr ⟨e, Finset.mem_insert_of_mem he, hve⟩

/-- **Lemma 7.2, one root**: at a binary or terminal root, a memory encoding with `g ≥ 1` labels
and at most `167g` edges. -/
theorem mem_encoding_nonUN [DecidableEq V] [Fintype C] (hC : Fintype.card C = 5)
    {ψ : C → V → ℤ} (hψ : S.IsPotential ψ 85 715)
    (hgrp : ∀ φ φ', S.IsTerm φ → S.IsTerm φ' → S.grp φ = S.grp φ' → ∀ c, ψ c φ = ψ c φ')
    (hUUU : ∀ θ, S.UN θ → S.UN (S.un θ) → ¬ S.UN (S.un (S.un θ)))
    {W : Type*} [DecidableEq W] [DecidableEq Γ] (nbr : W → Finset W) (f : V → W) (lab : W → Γ)
    (hlab : ∀ φ, S.IsTerm φ → lab (f φ) = S.grp φ)
    (hstep : ∀ a b, S.Step a b → f a ≠ f b → f b ∈ nbr (f a) ∧ f a ∈ nbr (f b))
    (hgl : ∀ φ φ', S.IsTerm φ → S.IsTerm φ' → S.grp φ = S.grp φ' → f φ ≠ f φ' →
      f φ' ∈ nbr (f φ))
    {ρ : V} (hρ : ¬ S.UN ρ) :
    ∃ g, 1 ≤ g ∧ ∃ K A, S.MemEnc nbr f lab ρ g (167 * g) K A := by
  classical
  by_cases hNF : S.NF ρ
  swap
  · refine ⟨1, le_rfl, ∅, {f ρ}, by simp, fun x y h => absurd h (Finset.notMem_empty _),
      fun e he => absurd he (Finset.notMem_empty _), fun v hv => Or.inl
      (Finset.mem_singleton.1 hv), by simp, fun v hv => ⟨ρ, ReflTransGen.refl, ⟨hNF, hρ⟩,
      Finset.mem_singleton.1 hv⟩⟩
  obtain ⟨P, hr, hval, hi, hcov, hconn, hcard⟩ := S.mem_contour hC hψ hgrp hUUU hNF
  have hC0 : Nonempty C := Fintype.card_pos_iff.mp (by omega)
  obtain ⟨c₀⟩ := hC0
  set K := ((S.witness P).image (Sym2.map f)).filter (fun e => ¬ e.IsDiag) with hK
  set A := (P ×ˢ (Finset.univ : Finset C)).image (fun p => f (S.pEnd p.1 p.2)) with hA
  have hP1 : 1 ≤ P.card := Finset.card_pos.2 ⟨_, hr⟩
  have hPNF : ∀ σ ∈ P, S.NF σ.loc := fun σ hσ => (hval σ hσ).2
  -- every arm end is reached in the witness
  have hend : ∀ σ ∈ P, ∀ c, FNE.EdgeCount.Reach (S.witness P) ρ (S.pEnd σ c) := by
    intro σ hσ c
    have hne : σ.loc ≠ S.pEnd σ c := by
      intro h
      have := S.pEnd_isTerm σ c
      rw [← h] at this
      exact this.1 (hPNF σ hσ)
    obtain ⟨d, hd, hvd⟩ := UND.Raw.exists_edge_of_reach (S.pEdges_reach σ c).2 hne
    exact hconn d (S.pEdges_subset_witness hσ c hd) _ hvd
  refine ⟨P.card, hP1, K, A, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (UND.Counting.card_image_filter_le f _).trans hcard
  · intro x y hxy
    obtain ⟨hmem, hnd⟩ := Finset.mem_filter.1 hxy
    obtain ⟨d, hd, hdxy⟩ := Finset.mem_image.1 hmem
    rcases Finset.mem_union.1 hd with hd | hd
    · obtain ⟨a, b, hab, rfl⟩ := S.armEdge_step P hPNF d hd
      rw [Sym2.map_mk] at hdxy
      have hfab : f a ≠ f b := by
        intro h
        rw [← hdxy, h] at hnd
        exact hnd (Sym2.mk_isDiag_iff.2 rfl)
      obtain ⟨h1, h2⟩ := hstep a b hab hfab
      rcases Sym2.eq_iff.mp hdxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact h1
      · exact h2
    · obtain ⟨σ, c, σ', c', hgg, rfl⟩ := S.grpEdge_spec P d hd
      rw [Sym2.map_mk] at hdxy
      have hfab : f (S.pEnd σ c) ≠ f (S.pEnd σ' c') := by
        intro h
        rw [← hdxy, h] at hnd
        exact hnd (Sym2.mk_isDiag_iff.2 rfl)
      rcases Sym2.eq_iff.mp hdxy with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
      · exact hgl _ _ (S.pEnd_isTerm σ c) (S.pEnd_isTerm σ' c') hgg hfab
      · exact hgl _ _ (S.pEnd_isTerm σ' c') (S.pEnd_isTerm σ c) hgg.symm (Ne.symm hfab)
  · exact UND.Counting.connectedAt_filter_not_diag (UND.Counting.connectedAt_image f hconn)
  · intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨hp1, -⟩ := Finset.mem_product.1 hp
    have hr' : FNE.EdgeCount.Reach K (f ρ) (f (S.pEnd p.1 p.2)) :=
      reach_filter_not_diag (reach_image f (hend p.1 hp1 p.2))
    by_cases he : f ρ = f (S.pEnd p.1 p.2)
    · exact Or.inl he.symm
    · exact Or.inr (UND.Raw.exists_edge_of_reach hr' he)
  · have e1 : A.image lab = (P ×ˢ (Finset.univ : Finset C)).image (fun p => S.pGrp p.1 p.2) := by
      rw [hA, Finset.image_image]
      refine Finset.image_congr fun p _ => ?_
      exact hlab _ (S.pEnd_isTerm p.1 p.2)
    have e2 : (P ×ˢ (Finset.univ : Finset C)).image (fun p => S.pGrp p.1 p.2) =
        P.image (fun σ => S.pGrp σ c₀) := by
      ext γ
      simp only [Finset.mem_image, Finset.mem_product, Finset.mem_univ, and_true, Prod.exists]
      constructor
      · rintro ⟨σ, c, hσ, rfl⟩
        obtain ⟨σ', hσ', h⟩ := hcov σ hσ c c₀
        exact ⟨σ', hσ', h⟩
      · rintro ⟨σ, hσ, rfl⟩
        exact ⟨σ, c₀, hσ, rfl⟩
    rw [e1, e2, Finset.card_image_of_injOn fun σ hσ σ' hσ' h => hi c₀ σ hσ σ' hσ' h]
  · intro v hv
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hv
    obtain ⟨hp1, -⟩ := Finset.mem_product.1 hp
    refine ⟨S.pEnd p.1 p.2, ?_, S.pEnd_isTerm p.1 p.2, rfl⟩
    exact (hval p.1 hp1).1.trans ((S.reach_sup (hPNF p.1 hp1) _).trans (S.reach_gEnd _ _))

theorem MemEnc.mono {W L : Type*} [DecidableEq L] {nbr : W → Finset W} {f : V → W} {lab : W → L}
    {ρ : V} {g n n' : ℕ} {K : Finset (Sym2 W)} {A : Finset W}
    (h : S.MemEnc nbr f lab ρ g n K A) (hn : n ≤ n') : S.MemEnc nbr f lab ρ g n' K A :=
  ⟨h.1.trans hn, h.2⟩

/-- A memory encoding is a literal encoding of Lemma 9.1. -/
theorem MemEnc.isEncoding {W L : Type*} [DecidableEq L] {nbr : W → Finset W} {f : V → W}
    {lab : W → L} {ρ : V} {g n : ℕ} {K : Finset (Sym2 W)} {A : Finset W}
    (h : S.MemEnc nbr f lab ρ g n K A) : UND.Counting.IsEncoding nbr (f ρ) n K A :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1⟩

/-- **Lemma 7.2, every root**: a memory encoding with `g ≥ 1` labels and at most `169g ≤ 256g`
edges (at most two unary links precede a binary or terminal vertex). -/
theorem mem_encoding [DecidableEq V] [Fintype C] (hC : Fintype.card C = 5)
    {ψ : C → V → ℤ} (hψ : S.IsPotential ψ 85 715)
    (hgrp : ∀ φ φ', S.IsTerm φ → S.IsTerm φ' → S.grp φ = S.grp φ' → ∀ c, ψ c φ = ψ c φ')
    (hUUU : ∀ θ, S.UN θ → S.UN (S.un θ) → ¬ S.UN (S.un (S.un θ)))
    {W : Type*} [DecidableEq W] [DecidableEq Γ] (nbr : W → Finset W) (f : V → W) (lab : W → Γ)
    (hlab : ∀ φ, S.IsTerm φ → lab (f φ) = S.grp φ)
    (hstep : ∀ a b, S.Step a b → f a ≠ f b → f b ∈ nbr (f a) ∧ f a ∈ nbr (f b))
    (hgl : ∀ φ φ', S.IsTerm φ → S.IsTerm φ' → S.grp φ = S.grp φ' → f φ ≠ f φ' →
      f φ' ∈ nbr (f φ))
    (ρ : V) : ∃ g, 1 ≤ g ∧ ∃ K A, S.MemEnc nbr f lab ρ g (256 * g) K A := by
  by_cases h0 : S.UN ρ
  · by_cases h1 : S.UN (S.un ρ)
    · obtain ⟨g, hg, K, A, hK⟩ := S.mem_encoding_nonUN hC hψ hgrp hUUU nbr f lab hlab hstep
        hgl (hUUU ρ h0 h1)
      obtain ⟨K1, hK1⟩ := S.prepend nbr f lab hstep (Or.inr ⟨h1, rfl⟩) hK
      obtain ⟨K2, hK2⟩ := S.prepend nbr f lab hstep (Or.inr ⟨h0, rfl⟩) hK1
      exact ⟨g, hg, K2, A, MemEnc.mono S hK2 (by omega)⟩
    · obtain ⟨g, hg, K, A, hK⟩ := S.mem_encoding_nonUN hC hψ hgrp hUUU nbr f lab hlab hstep
        hgl h1
      obtain ⟨K1, hK1⟩ := S.prepend nbr f lab hstep (Or.inr ⟨h0, rfl⟩) hK
      exact ⟨g, hg, K1, A, MemEnc.mono S hK1 (by omega)⟩
  · obtain ⟨g, hg, K, A, hK⟩ := S.mem_encoding_nonUN hC hψ hgrp hUUU nbr f lab hlab hstep
      hgl h0
    exact ⟨g, hg, K, A, MemEnc.mono S hK (by omega)⟩

end UND.Contour.GroupedSystem

namespace UND.Memory

/-- **Lemma 7.2 with Lemma 6.3 (the union bound)**: if every outcome of `Ev` has a literal
encoding (at most `256g` edges, graph of degree `≤ Δ ≤ Δ_paper`) whose marked set carries exactly
`g ≥ 1` labels, each a source (`R ∪ S`), and the joint source law gives `γ^{|G|}` for every finite
set `G` of labels, then `μ(Ev) ≤ Σ_{g ≥ 1} (K_mem γ)^g`. -/
theorem mem_union {Ω W L : Type*} [DecidableEq W] [DecidableEq L] [MeasurableSpace Ω]
    (μ : Measure Ω) (nbr : W → Finset W) (Δ : ℕ) (hΔ : ∀ a, (nbr a).card ≤ Δ) (hΔ1 : 1 ≤ Δ)
    (hΔD : Δ ≤ UND.Param.Delta) (z : W) (lab : W → L) (R Sv : L → Set Ω) (γ : ℝ≥0∞)
    (hJ : ∀ G : Finset L, μ (⋂ l ∈ G, (R l ∪ Sv l)) ≤ γ ^ G.card) (Ev : Set Ω)
    (hEv : ∀ ω ∈ Ev, ∃ g, 1 ≤ g ∧ ∃ K A, UND.Counting.IsEncoding nbr z (256 * g) K A ∧
      (A.image lab).card = g ∧ ∀ v ∈ A, ω ∈ R (lab v) ∪ Sv (lab v)) :
    μ Ev ≤ ∑' g : ℕ, ((UND.Param.Kmem : ℝ≥0∞) * γ) ^ (g + 1) := by
  classical
  refine UND.Counting.measure_le_tsum_groups μ nbr Δ 256 UND.Param.Kmem hΔ hΔ1
    (fun g hg => UND.Counting.four_le_Kmem_pow_of_le hΔD g hg) z
    (fun g _K A => if (A.image lab).card = g then ⋂ l ∈ A.image lab, (R l ∪ Sv l) else ∅) γ
    ?_ Ev ?_
  · intro g _ K A _
    by_cases hc : (A.image lab).card = g
    · simp only [hc, ↓reduceIte]
      rw [← hc]
      exact hJ _
    · simp [hc]
  · intro ω hω
    obtain ⟨g, hg, K, A, hKA, hc, hmem⟩ := hEv ω hω
    refine ⟨g, hg, K, A, hKA, ?_⟩
    simp only [hc, ↓reduceIte, Set.mem_iInter, Finset.mem_image]
    rintro l ⟨v, hv, rfl⟩
    exact hmem v hv

end UND.Memory
