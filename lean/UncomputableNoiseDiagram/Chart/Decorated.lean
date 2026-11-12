/-
# Section 3.2: rank flags (S3, the decorated scaffold) and Lemma 3.2 (S4)

Nodes S3 and S4 of `BLUEPRINT.md` (Part A.3), NEW.

Paper (Section 3.2): "Add a column bit `V` and a row bit `H_row` before quartering. Copy `V` on
north/south edge colours and `H_row` on east/west colours. Impose
`A: V = H_row; B, C: V ≥ H_row; D, E: V ≤ H_row` (8). Internal quarter edges compare the whole
decorated parent; external edges compare its edge colours. This is a finite Wang construction.

**Lemma 3.2.** In any legal decorated chart the flags at finite ranks have one common
nonincreasing value sequence `(b_r)_{r ≥ 0}`. Every finite cutoff `b_r = 1{r < c}` occurs over every
typical scaffold chart."

Formalization (REUSE of the hard-model core's quarters `UPD.Scaffold.Quarter`, their colours and
`Quarter.matchE_iff`/`matchN_iff`):

* `rankOK` (the filter (8)), `DTriple` (a letter of `𝔸` with the bits `V`, `H_row`), `DLetter` (the
  decorated parents passing (8)), `DQuarter` (a quadrant and a decorated parent) with the Wang
  colours of the quartering (`colE`, `colW`, `colN`, `colS`: internal edges carry the whole
  decorated parent, external edges its edge colours with `V` on north/south and `H_row` on
  east/west), `DQuarter.MatchE`, `MatchN`, and their characterizations `matchE_iff`, `matchN_iff`;
* `DQuarter.toQ` (forget the bits): legal decorated charts project to tilings of `𝔸^q`
  (`isQTiling_toQ`); `H_row` is constant along rows and `V` along columns (`H_row_const`,
  `V_col_const`);
* **`cutoff_of_dtiling`** (Lemma 3.2, first sentence): one common nonincreasing sequence `(b_r)`
  gives the column bits at parent rank `r` and the row bits at parent rank `r`, in every phase;
* **`cutoff_exists`** (Lemma 3.2, second sentence): over every scaffold chart whose two phase
  coordinates are not integers (every parent rank is finite: the typical charts), every finite
  cutoff `b_r = 1{r < c}` is realized by a legal decorated chart over it.
-/
import UncomputableNoiseDiagram.Chart.BlackType
import UncomputableNoiseDiagram.Chart.Origins

set_option autoImplicit false

namespace UND.Chart

open UPD UPD.Scaffold

/-- (8), the rank filter on a decorated parent of black type `ψ`: `A`: `V = H_row`; `B, C`:
`V ≥ H_row`; `D, E`: `V ≤ H_row`. -/
def rankOK : Black → Bool → Bool → Bool
  | .A, V, H => V == H
  | .B, V, H => V || !H
  | .C, V, H => V || !H
  | .D, V, H => H || !V
  | .E, V, H => H || !V

/-- A decorated parent before the filter: a letter of `𝔸`, the column bit `V` and the row bit
`H_row`. -/
structure DTriple where
  /-- the scaffold letter -/
  a : LetterA
  /-- the column bit `V` -/
  V : Bool
  /-- the row bit `H_row` -/
  H : Bool
  deriving DecidableEq, Fintype

/-- The decorated parents: the triples passing the filter (8). -/
abbrev DLetter := {x : DTriple // rankOK x.a.1.base.black x.V x.H = true}

/-- A decorated quarter: a quadrant and a decorated parent (quartering after decoration). -/
structure DQuarter where
  /-- the quadrant `ς` -/
  quad : Bool × Bool
  /-- the decorated parent -/
  parent : DLetter
  deriving DecidableEq, Fintype

/-- East/west colours of decorated quarters (marks `∘`, `•` as the two summands). -/
abbrev DColH := (DLetter ⊕ (((HAtom × HAtom × Bool) × Bool) × Bool)) × Bool

/-- North/south colours of decorated quarters. -/
abbrev DColV := (DLetter ⊕ (((VAtom × VAtom × Bool) × Bool) × Bool)) × Bool

namespace DQuarter

/-- East colour: the whole decorated parent on an internal edge (`ς₁ = 0`); on an external edge
(`ς₁ = 1`) the parent's east colour with `H_row`. -/
def colE (q : DQuarter) : DColH :=
  if q.quad.1 = false then (.inl q.parent, q.quad.2)
  else (.inr (q.parent.1.a.1.colE, q.parent.1.H), q.quad.2)

/-- West colour. -/
def colW (q : DQuarter) : DColH :=
  if q.quad.1 = true then (.inl q.parent, q.quad.2)
  else (.inr (q.parent.1.a.1.colW, q.parent.1.H), q.quad.2)

/-- North colour: the whole decorated parent on an internal edge (`ς₂ = 0`); on an external edge
the parent's north colour with `V`. -/
def colN (q : DQuarter) : DColV :=
  if q.quad.2 = false then (.inl q.parent, q.quad.1)
  else (.inr (q.parent.1.a.1.colN, q.parent.1.V), q.quad.1)

/-- South colour. -/
def colS (q : DQuarter) : DColV :=
  if q.quad.2 = true then (.inl q.parent, q.quad.1)
  else (.inr (q.parent.1.a.1.colS, q.parent.1.V), q.quad.1)

/-- Horizontal matching (`q'` east of `q`). -/
def MatchE (q q' : DQuarter) : Prop := q.colE = q'.colW

/-- Vertical matching (`q'` north of `q`). -/
def MatchN (q q' : DQuarter) : Prop := q.colN = q'.colS

instance : DecidableRel MatchE := fun q q' => inferInstanceAs (Decidable (q.colE = q'.colW))

instance : DecidableRel MatchN := fun q q' => inferInstanceAs (Decidable (q.colN = q'.colS))

/-- The underlying quarter of `𝔸^q` (forget the bits). -/
def toQ (q : DQuarter) : Quarter := ⟨q.quad, q.parent.1.a⟩

/-- The column bit `V`. -/
def V (q : DQuarter) : Bool := q.parent.1.V

/-- The row bit `H_row`. -/
def H (q : DQuarter) : Bool := q.parent.1.H

theorem matchE_iff (q q' : DQuarter) :
    MatchE q q' ↔ q'.quad.1 = !q.quad.1 ∧ q'.quad.2 = q.quad.2 ∧
      ((q.quad.1 = false ∧ q'.parent = q.parent) ∨
        (q.quad.1 = true ∧ Letter.MatchE q.parent.1.a.1 q'.parent.1.a.1 ∧
          q'.parent.1.H = q.parent.1.H)) := by
  obtain ⟨⟨s1, s2⟩, p⟩ := q
  obtain ⟨⟨t1, t2⟩, p'⟩ := q'
  cases s1 <;> cases t1 <;>
    simp [MatchE, colE, colW, Letter.MatchE, eq_comm, and_comm]

theorem matchN_iff (q q' : DQuarter) :
    MatchN q q' ↔ q'.quad.2 = !q.quad.2 ∧ q'.quad.1 = q.quad.1 ∧
      ((q.quad.2 = false ∧ q'.parent = q.parent) ∨
        (q.quad.2 = true ∧ Letter.MatchN q.parent.1.a.1 q'.parent.1.a.1 ∧
          q'.parent.1.V = q.parent.1.V)) := by
  obtain ⟨⟨s1, s2⟩, p⟩ := q
  obtain ⟨⟨t1, t2⟩, p'⟩ := q'
  cases s2 <;> cases t2 <;>
    simp [MatchN, colN, colS, Letter.MatchN, eq_comm, and_comm]

theorem toQ_matchE {q q' : DQuarter} (h : MatchE q q') : Quarter.MatchE q.toQ q'.toQ := by
  rw [matchE_iff] at h
  rw [Quarter.matchE_iff]
  obtain ⟨h1, h2, ⟨h3, h4⟩ | ⟨h3, h4, -⟩⟩ := h
  · exact ⟨h1, h2, Or.inl ⟨h3, by simp only [toQ, h4]⟩⟩
  · exact ⟨h1, h2, Or.inr ⟨h3, h4⟩⟩

theorem toQ_matchN {q q' : DQuarter} (h : MatchN q q') : Quarter.MatchN q.toQ q'.toQ := by
  rw [matchN_iff] at h
  rw [Quarter.matchN_iff]
  obtain ⟨h1, h2, ⟨h3, h4⟩ | ⟨h3, h4, -⟩⟩ := h
  · exact ⟨h1, h2, Or.inl ⟨h3, by simp only [toQ, h4]⟩⟩
  · exact ⟨h1, h2, Or.inr ⟨h3, h4⟩⟩

/-- `H_row` is copied across every horizontal edge. -/
theorem H_eq_of_matchE {q q' : DQuarter} (h : MatchE q q') : q'.H = q.H := by
  rw [matchE_iff] at h
  obtain ⟨-, -, ⟨-, h4⟩ | ⟨-, -, h4⟩⟩ := h
  · simp only [H, h4]
  · exact h4

/-- `V` is copied across every vertical edge. -/
theorem V_eq_of_matchN {q q' : DQuarter} (h : MatchN q q') : q'.V = q.V := by
  rw [matchN_iff] at h
  obtain ⟨-, -, ⟨-, h4⟩ | ⟨-, -, h4⟩⟩ := h
  · simp only [V, h4]
  · exact h4

end DQuarter

/-- A legal decorated chart: a tiling by decorated quarters. -/
def IsDTiling (Z : Plane → DQuarter) : Prop :=
  LegalOn DQuarter.MatchE DQuarter.MatchN Set.univ Z

/-- A legal decorated chart projects to a tiling of `𝔸^q`. -/
theorem isQTiling_toQ {Z : Plane → DQuarter} (hZ : IsDTiling Z) :
    IsQTiling (fun ξ => (Z ξ).toQ) :=
  hZ.map DQuarter.toQ (fun _ _ h => DQuarter.toQ_matchE h) (fun _ _ h => DQuarter.toQ_matchN h)

/-- "Rows carry constant bits by edge matching": `H_row` is constant along each row. -/
theorem H_row_const {Z : Plane → DQuarter} (hZ : IsDTiling Z) (x y : ℤ) :
    (Z (x, y)).H = (Z (0, y)).H := by
  have step : ∀ i : ℤ, (Z (i + 1, y)).H = (Z (i, y)).H := fun i => by
    have h := hZ.1 (i, y) (Set.mem_univ _) (Set.mem_univ _)
    simp only [Prod.mk_add_mk, add_zero] at h
    exact DQuarter.H_eq_of_matchE h
  induction x using Int.induction_on with
  | zero => rfl
  | succ i ih => rw [step, ih]
  | pred i ih =>
    have h := step (-(i : ℤ) - 1)
    rw [sub_add_cancel] at h
    rw [← h, ih]

/-- Columns carry constant bits: `V` is constant along each column. -/
theorem V_col_const {Z : Plane → DQuarter} (hZ : IsDTiling Z) (x y : ℤ) :
    (Z (x, y)).V = (Z (x, 0)).V := by
  have step : ∀ i : ℤ, (Z (x, i + 1)).V = (Z (x, i)).V := fun i => by
    have h := hZ.2 (x, i) (Set.mem_univ _) (Set.mem_univ _)
    simp only [Prod.mk_add_mk, add_zero] at h
    exact DQuarter.V_eq_of_matchN h
  induction y using Int.induction_on with
  | zero => rfl
  | succ i ih => rw [step, ih]
  | pred i ih =>
    have h := step (-(i : ℤ) - 1)
    rw [sub_add_cancel] at h
    rw [← h, ih]

/-- The filter (8) at a parent of the black type forced by the ranks: the comparisons of
`cutoff_of_filter`. -/
theorem filter_of_black {ψ : Black} {V H : Bool} (hok : rankOK ψ V H = true) {r s : ℕ}
    (hb : (r = s → ψ = .A) ∧ (r < s → ψ = .B ∨ ψ = .C) ∧ (s < r → ψ = .D ∨ ψ = .E)) :
    (r = s → V = H) ∧ (r < s → H ≤ V) ∧ (s < r → V ≤ H) := by
  refine ⟨fun h => ?_, fun h => ?_, fun h => ?_⟩
  · rw [hb.1 h] at hok
    cases V <;> cases H <;> simp_all [rankOK]
  · rcases hb.2.1 h with e | e <;> rw [e] at hok <;> cases V <;> cases H <;> simp_all [rankOK]
  · rcases hb.2.2 h with e | e <;> rw [e] at hok <;> cases V <;> cases H <;> simp_all [rankOK]

/-- Every parent rank occurs on every axis, as the parent rank of a physical coordinate. -/
theorem exists_prank (t : ℕ → Bool) (r : ℕ) : ∃ z, PRank t z r := by
  obtain ⟨u, hu⟩ := exists_rank (fun m => t (m + 1)) r
  refine ⟨2 * u + bitZ (t 0), ?_⟩
  have e : (2 * u + bitZ (t 0) - bitZ (t 0)) / 2 = u := by omega
  unfold PRank
  rw [e]
  exact hu

/-- **Lemma 3.2, first sentence.** In any legal decorated chart, in every phase `τ` of its
scaffold, one common nonincreasing sequence `(b_r)` gives the column bit at every coordinate of
parent rank `r` and the row bit at every coordinate of parent rank `r`. -/
theorem cutoff_of_dtiling {Z : Plane → DQuarter} (hZ : IsDTiling Z) {τ : ℕ → Bool × Bool}
    (hτ : IsQPhase (fun ξ => (Z ξ).toQ) τ) :
    ∃ b : ℕ → Bool, Antitone b ∧
      (∀ ξ r, PRank (col τ) ξ.1 r → (Z ξ).V = b r) ∧
      (∀ ξ s, PRank (row τ) ξ.2 s → (Z ξ).H = b s) := by
  obtain ⟨f, -, hYf, F, hF, hF0⟩ := hτ
  have hpar : ∀ ξ : Plane, (Z ξ).parent.1.a.1 = F 0 (half (ξ - bvec (τ 0))) := by
    intro ξ
    have e := congrArg (fun q : Quarter => q.parent.1) (congrFun hYf ξ)
    rw [hF0]
    exact e
  have hfilter : ∀ z y r s, PRank (col τ) z r → PRank (row τ) y s →
      (r = s → (Z (z, 0)).V = (Z (0, y)).H) ∧ (r < s → (Z (0, y)).H ≤ (Z (z, 0)).V) ∧
      (s < r → (Z (z, 0)).V ≤ (Z (0, y)).H) := by
    intro z y r s hr hs
    have hb := black_rank_compare (hF.towerRel (min r s + 1)) (x := half ((z, y) - bvec (τ 0)))
      hr hs (by omega)
    have hok := (Z (z, y)).parent.2
    rw [← V_col_const hZ z y, ← H_row_const hZ z y]
    rw [hpar] at hok
    exact filter_of_black hok hb
  obtain ⟨b, hb, hbc, hbr⟩ := cutoff_of_filter (PRank (col τ)) (PRank (row τ))
    (fun z => (Z (z, 0)).V) (fun y => (Z (0, y)).H) hfilter (exists_prank (col τ))
    (exists_prank (row τ))
  refine ⟨b, hb, fun ξ r hr => ?_, fun ξ s hs => ?_⟩
  · obtain ⟨x, y⟩ := ξ
    rw [V_col_const hZ x y]
    exact hbc x r hr
  · obtain ⟨x, y⟩ := ξ
    rw [H_row_const hZ x y]
    exact hbr y s hs

/-- **Lemma 3.2, second sentence.** Over every scaffold chart whose phase coordinates are not
integers (so every parent rank is finite: the typical charts), every finite cutoff
`b_r = 1{r < c}` is realized by a legal decorated chart. -/
theorem cutoff_exists {Y : Plane → Quarter} {τ : ℕ → Bool × Bool} (hY : IsQPhase Y τ)
    (hc : NotInt (col τ)) (hr : NotInt (row τ)) (c : ℕ) :
    ∃ Z : Plane → DQuarter, IsDTiling Z ∧ (∀ ξ, (Z ξ).toQ = Y ξ) ∧
      (∀ ξ r, PRank (col τ) ξ.1 r → (Z ξ).V = decide (r < c)) ∧
      (∀ ξ s, PRank (row τ) ξ.2 s → (Z ξ).H = decide (s < c)) := by
  have hYt : IsQTiling Y := by
    obtain ⟨f, hf, rfl, -⟩ := hY
    exact isQTiling_qshift hf _
  obtain ⟨f, -, hYf, F, hF, hF0⟩ := hY
  choose rkc hrkc using (NotInt.tail hc).exists_rank
  choose rkr hrkr using (NotInt.tail hr).exists_rank
  set bc : ℤ := bitZ (τ 0).1 with hbc
  set br : ℤ := bitZ (τ 0).2 with hbr
  have hpar : ∀ ξ : Plane, (Y ξ).parent.1 = F 0 (half (ξ - bvec (τ 0))) := by
    intro ξ; rw [hYf, hF0]; rfl
  have hquad : ∀ ξ : Plane, (Y ξ).quad =
      (decide ((ξ.1 - bc) % 2 = 1), decide ((ξ.2 - br) % 2 = 1)) := by
    intro ξ; rw [hYf]; rfl
  have hok : ∀ ξ : Plane, rankOK (Y ξ).parent.1.base.black (decide (rkc ((ξ.1 - bc) / 2) < c))
      (decide (rkr ((ξ.2 - br) / 2) < c)) = true := by
    intro ξ
    have hb := black_rank_compare
      (hF.towerRel (min (rkc ((ξ.1 - bc) / 2)) (rkr ((ξ.2 - br) / 2)) + 1))
      (x := half (ξ - bvec (τ 0))) (hrkc ((ξ.1 - bc) / 2)) (hrkr ((ξ.2 - br) / 2)) (by omega)
    rw [hpar]
    rcases lt_trichotomy (rkc ((ξ.1 - bc) / 2)) (rkr ((ξ.2 - br) / 2)) with h | h | h
    · rcases hb.2.1 h with e | e <;> rw [e] <;> simp [rankOK] <;> omega
    · rw [hb.1 h, h]; simp [rankOK]
    · rcases hb.2.2 h with e | e <;> rw [e] <;> simp [rankOK] <;> omega
  let Z : Plane → DQuarter := fun ξ =>
    ⟨(Y ξ).quad, ⟨⟨(Y ξ).parent, decide (rkc ((ξ.1 - bc) / 2) < c),
      decide (rkr ((ξ.2 - br) / 2) < c)⟩, hok ξ⟩⟩
  refine ⟨Z, ⟨fun ξ _ _ => ?_, fun ξ _ _ => ?_⟩, fun ξ => rfl, fun ξ r hr' => ?_,
    fun ξ s hs => ?_⟩
  · -- horizontal edges
    have hq := (Quarter.matchE_iff _ _).1 (hYt.1 ξ (Set.mem_univ _) (Set.mem_univ _))
    rw [DQuarter.matchE_iff]
    obtain ⟨h1, h2, h3⟩ := hq
    have e2 : (ξ + (1, 0)).2 = ξ.2 := by simp
    refine ⟨h1, h2, ?_⟩
    rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · refine Or.inl ⟨h3, ?_⟩
      have hev : (ξ.1 - bc) % 2 = 0 := by
        have h' := congrArg Prod.fst (hquad ξ)
        rw [h3] at h'
        have h'' : ¬ (ξ.1 - bc) % 2 = 1 := by simpa using h'.symm
        omega
      have e1 : ((ξ + (1, 0)).1 - bc) / 2 = (ξ.1 - bc) / 2 := by
        simp only [Prod.fst_add]
        omega
      apply Subtype.ext
      show DTriple.mk _ _ _ = DTriple.mk _ _ _
      rw [h4, e1, e2]
    · refine Or.inr ⟨h3, h4, ?_⟩
      show decide (rkr (((ξ + (1, 0)).2 - br) / 2) < c) = decide (rkr ((ξ.2 - br) / 2) < c)
      rw [e2]
  · -- vertical edges
    have hq := (Quarter.matchN_iff _ _).1 (hYt.2 ξ (Set.mem_univ _) (Set.mem_univ _))
    rw [DQuarter.matchN_iff]
    obtain ⟨h1, h2, h3⟩ := hq
    have e1 : (ξ + (0, 1)).1 = ξ.1 := by simp
    refine ⟨h1, h2, ?_⟩
    rcases h3 with ⟨h3, h4⟩ | ⟨h3, h4⟩
    · refine Or.inl ⟨h3, ?_⟩
      have hev : (ξ.2 - br) % 2 = 0 := by
        have h' := congrArg Prod.snd (hquad ξ)
        rw [h3] at h'
        have h'' : ¬ (ξ.2 - br) % 2 = 1 := by simpa using h'.symm
        omega
      have e2 : ((ξ + (0, 1)).2 - br) / 2 = (ξ.2 - br) / 2 := by
        simp only [Prod.snd_add]
        omega
      apply Subtype.ext
      show DTriple.mk _ _ _ = DTriple.mk _ _ _
      rw [h4, e1, e2]
    · refine Or.inr ⟨h3, h4, ?_⟩
      show decide (rkc (((ξ + (0, 1)).1 - bc) / 2) < c) = decide (rkc ((ξ.1 - bc) / 2) < c)
      rw [e1]
  · show decide (rkc ((ξ.1 - bc) / 2) < c) = decide (r < c)
    rw [(hrkc ((ξ.1 - bc) / 2)).unique hr']
  · show decide (rkr ((ξ.2 - br) / 2) < c) = decide (s < c)
    rw [(hrkr ((ξ.2 - br) / 2)).unique hs]

end UND.Chart
