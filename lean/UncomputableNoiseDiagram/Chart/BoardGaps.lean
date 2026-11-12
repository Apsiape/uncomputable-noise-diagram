/-
# Lemma 3.3: non-free lines of a board carry only one direction (the laminar argument, S8)

Part of node S8 of `BLUEPRINT.md` (Part A.3), NEW (REUSE of the hard-model core's frame lemmas
`frames_contain`, `endpoint_not_inFrame`, `frame_window_unique`).

Paper (Lemma 3.3, proof, third and fourth paragraphs): "For `z ∈ (L_*, R_*)` let
`D_z = {e : 1 ≤ e ≤ d, z lies in a depth-e column frame}`, `e_z = min D_z`. … Consider all depth-`e`
row frames with `e ∈ D_z` meeting `[Bot_*, Top_*]`. They form a finite strictly laminar family …
their endpoints are exactly the horizontal walls on this strip. Its minimal members are exactly its
depth-`e_z` members … Consecutive endpoints labelled B then T bound exactly a minimal member. …
The vertical orientation rule forces each gap's pair from its two endpoint labels. Hence vertical
carriers are exactly the interiors of those minimal frames. … If `z` is not free, then `e_z < d`,
while `y_j` lies in no depth-`e_z` frame, so `(z, y_j)` is horizontal only."

The formal route uses only what the board needs: at a wall-free site of a free row with orientation
`(B, T)`, the nearest walls below and above are a bottom and a top wall with no wall between
(`exists_gap`, the orientation rule along the gap); then the frame of the top wall reaches down to
the bottom wall, which forces both to be the board's own endpoints (`laminar_gap`); a column that is
not free carries a smaller frame's walls strictly inside, a contradiction.

* `exists_gap` (generic in the axis): the gap of a wall-free site with orientation `(lo, hi)`;
* `laminar_gap` (generic in the axis): no `lo`–`hi` gap of a non-free line contains a free
  coordinate of the board;
* **`board_not_vcarrier`**: on a free row, the sites of non-free columns of the open board are not
  vertical carriers (they are horizontal only, with `board_row`);
* **`board_not_hcarrier`**: the transposed statement.
-/
import UncomputableNoiseDiagram.Chart.Board

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UND.Chart

open UPD UPD.Scaffold

/-- **The gap of a wall-free site** (one axis). On `[L, R]` with walls at both ends, a wall-free
interior site whose orientation pair is `(lab lo, lab hi)` lies strictly between a `lo` wall and a
`hi` wall with no wall between them. -/
theorem exists_gap {α : Type*} (W : ℤ → Option Side) (o1 o2 : ℤ → α × α) (lab : Side → α)
    (hlab : Function.Injective lab) (hm : ∀ z, o2 z = o1 (z + 1))
    (hnone : ∀ z, W z = none → o1 z = o2 z)
    (hwall : ∀ z σ, W z = some σ → (o2 z).1 = lab σ ∧ (o1 z).2 = lab σ)
    {L R y : ℤ} (hL : W L ≠ none) (hR : W R ≠ none) (hLy : L < y) (hyR : y < R)
    (hy : W y = none) (ho : o1 y = (lab .lo, lab .hi)) :
    ∃ ylo yhi, L ≤ ylo ∧ ylo < y ∧ y < yhi ∧ yhi ≤ R ∧ W ylo = some .lo ∧ W yhi = some .hi ∧
      ∀ z, ylo < z → z < yhi → W z = none := by
  classical
  have hexL : ∃ i : ℕ, W (y - 1 - i) ≠ none :=
    ⟨(y - 1 - L).toNat, by rw [show y - 1 - ((y - 1 - L).toNat : ℤ) = L by omega]; exact hL⟩
  have hexR : ∃ j : ℕ, W (y + 1 + j) ≠ none :=
    ⟨(R - y - 1).toNat, by rw [show y + 1 + ((R - y - 1).toNat : ℤ) = R by omega]; exact hR⟩
  set i₀ := Nat.find hexL with hi₀
  set j₀ := Nat.find hexR with hj₀
  have hi₀le : i₀ ≤ (y - 1 - L).toNat := Nat.find_min' hexL
    (by rw [show y - 1 - ((y - 1 - L).toNat : ℤ) = L by omega]; exact hL)
  have hj₀le : j₀ ≤ (R - y - 1).toNat := Nat.find_min' hexR
    (by rw [show y + 1 + ((R - y - 1).toNat : ℤ) = R by omega]; exact hR)
  have hWlo : W (y - 1 - i₀) ≠ none := Nat.find_spec hexL
  have hWhi : W (y + 1 + j₀) ≠ none := Nat.find_spec hexR
  have hgap : ∀ z, y - 1 - i₀ < z → z < y + 1 + j₀ → W z = none := by
    intro z h1 h2
    rcases lt_trichotomy z y with hz | rfl | hz
    · have := Nat.find_min hexL (m := (y - 1 - z).toNat) (by omega)
      rw [show y - 1 - ((y - 1 - z).toNat : ℤ) = z by omega] at this
      simpa using this
    · exact hy
    · have := Nat.find_min hexR (m := (z - y - 1).toNat) (by omega)
      rw [show y + 1 + ((z - y - 1).toNat : ℤ) = z by omega] at this
      simpa using this
  obtain ⟨σlo, hσlo⟩ := Option.ne_none_iff_exists'.1 hWlo
  obtain ⟨σhi, hσhi⟩ := Option.ne_none_iff_exists'.1 hWhi
  have hor := strip_orient W o1 o2 (lab σlo) (lab σhi) hm hnone (hwall _ _ hσlo).1
    (hwall _ _ hσhi).2 hgap y (by omega) (by omega)
  rw [ho] at hor
  obtain ⟨e1, e2⟩ := Prod.mk.inj hor.1
  have h1 : σlo = .lo := hlab e1.symm
  have h2 : σhi = .hi := hlab e2.symm
  subst h1 h2
  exact ⟨_, _, by omega, by omega, by omega, by omega, hσlo, hσhi, hgap⟩

/-- **The laminar argument** (one axis). Along a line whose walls at coordinates `z` of finite
parent rank are the endpoints of the depth-`e` frames with `P e` (`lo` for left, `hi` for right
endpoints), where `P` holds at the board depth `d` and at some smaller depth `e₀ ≥ 1`: no `lo`–`hi`
gap inside the closed board frame contains a free coordinate of the board. -/
theorem laminar_gap (t : ℕ → Bool) (P : ℕ → Prop) (W : ℤ → Option Side) {d : ℕ} (m : ℤ)
    (hW : ∀ z σ, (∃ r, PRank t z r) → (W z = some σ ↔ ∃ e, 1 ≤ e ∧
      ((σ = .lo ∧ IsLeftEnd (phaseOffsets t) e z) ∨ (σ = .hi ∧ IsRightEnd (phaseOffsets t) e z)) ∧
        P e))
    {e₀ : ℕ} (he₀ : 1 ≤ e₀) (he₀d : e₀ < d) (hPe₀ : P e₀)
    {y : ℤ} (hy : IsFree (phaseOffsets t) d m y)
    {ylo yhi : ℤ} (h1 : ylo < y) (h2 : y < yhi) (hlo : W ylo = some .lo) (hhi : W yhi = some .hi)
    (hgap : ∀ z, ylo < z → z < yhi → W z = none)
    (hBot : frameLo (phaseOffsets t) d m ≤ ylo) (hTop : yhi ≤ frameHi (phaseOffsets t) d m) :
    False := by
  set a := phaseOffsets t with ha
  have hfa : FrameOffsets a := frameOffsets_phase t
  have rank_of_end : ∀ {e z}, (IsLeftEnd a e z ∨ IsRightEnd a e z) → ∃ r, PRank t z r := by
    intro e z h
    rcases h with h | h
    · obtain ⟨r, -, hr⟩ := exists_prank_le_of_inFrame t (inFrame_of_isLeftEnd h); exact ⟨r, hr⟩
    · obtain ⟨r, -, hr⟩ := exists_prank_le_of_inFrame t (inFrame_of_isRightEnd h); exact ⟨r, hr⟩
  have hy1 : frameLo a d m < y := hy.1
  have hy2 : y < frameHi a d m := hy.2.1
  -- the frame of the bottom wall `ylo`
  obtain ⟨e, he, hend, hPe⟩ := (hW ylo .lo (by
    obtain ⟨r, -, hr⟩ := exists_prank_le_of_inFrame t
      (⟨m, hBot, by omega⟩ : InFrame a d ylo)
    exact ⟨r, hr⟩)).1 hlo
  have hylo : IsLeftEnd a e ylo := by
    rcases hend with ⟨-, h⟩ | ⟨h, -⟩
    · exact h
    · cases h
  obtain ⟨mI, hmI⟩ := hylo
  -- its top endpoint is a `hi` wall, hence at or above `yhi`
  have hItop : W (frameHi a e mI) = some .hi :=
    (hW _ .hi (rank_of_end (Or.inr ⟨mI, rfl⟩))).2 ⟨e, he, Or.inr ⟨rfl, ⟨mI, rfl⟩⟩, hPe⟩
  have hIlt : ylo < frameHi a e mI := by rw [hmI]; exact frameLo_lt_frameHi a e mI
  have hIge : yhi ≤ frameHi a e mI := by
    by_contra hlt
    push Not at hlt
    rw [hgap _ hIlt hlt] at hItop
    cases hItop
  -- so `y` lies in that frame: its depth is `d` and `ylo` is the board's bottom endpoint
  have hey : ¬ e < d := fun hlt => hy.2.2 e he hlt ⟨mI, by omega, by omega⟩
  have hed : e ≤ d := le_of_end_inFrame t (Or.inl ⟨mI, hmI⟩)
    (⟨m, hBot, by omega⟩ : InFrame a d ylo)
  obtain rfl : e = d := by omega
  have hm : mI = m := frame_window_unique (a := a) (d := e) (z := ylo)
    ⟨by rw [hmI], by rw [hmI]; exact (frameLo_lt_frameHi a e mI).le⟩ ⟨hBot, by omega⟩
  subst hm
  -- the frame of the top wall `yhi` reaches down to `ylo`, so it is the board frame
  obtain ⟨e', he', hend', hPe'⟩ := (hW yhi .hi (by
    obtain ⟨r, -, hr⟩ := exists_prank_le_of_inFrame t
      (⟨mI, by omega, hTop⟩ : InFrame a e yhi)
    exact ⟨r, hr⟩)).1 hhi
  have hyhi : IsRightEnd a e' yhi := by
    rcases hend' with ⟨h, -⟩ | ⟨-, h⟩
    · cases h
    · exact h
  obtain ⟨mJ, hmJ⟩ := hyhi
  have hJbot : W (frameLo a e' mJ) = some .lo :=
    (hW _ .lo (rank_of_end (Or.inl ⟨mJ, rfl⟩))).2 ⟨e', he', Or.inl ⟨rfl, ⟨mJ, rfl⟩⟩, hPe'⟩
  have hJlt : frameLo a e' mJ < yhi := by rw [hmJ]; exact frameLo_lt_frameHi a e' mJ
  have hJle : frameLo a e' mJ ≤ ylo := by
    by_contra hlt
    push Not at hlt
    rw [hgap _ hlt hJlt] at hJbot
    cases hJbot
  have hey' : ¬ e' < e := fun hlt => hy.2.2 e' he' hlt ⟨mJ, by omega, by omega⟩
  have hed' : e' ≤ e := le_of_end_inFrame t (Or.inr ⟨mJ, hmJ⟩)
    (⟨mI, by omega, hTop⟩ : InFrame a e yhi)
  obtain rfl : e' = e := by omega
  have hm' : mJ = mI := frame_window_unique (a := a) (d := e') (z := yhi)
    ⟨by rw [hmJ]; exact (frameLo_lt_frameHi a e' mJ).le, by rw [hmJ]⟩
    ⟨by omega, hTop⟩
  subst hm'
  -- a smaller frame of the line lies strictly inside the board frame: its bottom wall is in the gap
  obtain ⟨mK, hK1, hK2⟩ := frames_contain a he₀d mJ
  have hne : frameLo a e₀ mK ≠ frameLo a e' mJ := by
    intro heq
    exact (endpoint_not_inFrame hfa he₀d mJ).1
      ⟨mK, by rw [heq], by rw [← heq]; exact (frameLo_lt_frameHi a e₀ mK).le⟩
  have hKbot : W (frameLo a e₀ mK) = some .lo :=
    (hW _ .lo (rank_of_end (Or.inl ⟨mK, rfl⟩))).2 ⟨e₀, he₀, Or.inl ⟨rfl, ⟨mK, rfl⟩⟩, hPe₀⟩
  have hKlo : ylo < frameLo a e₀ mK := by rw [hmI]; omega
  have hKhi : frameLo a e₀ mK < yhi := by
    have := frameLo_lt_frameHi a e₀ mK
    rw [hmJ]; omega
  rw [hgap _ hKlo hKhi] at hKbot
  cases hKbot

/-- Sides of horizontal walls as `Side`. -/
def BT.side : BT → Side
  | .B => .lo
  | .T => .hi

/-- Sides of vertical walls as `Side`. -/
def LR.side : LR → Side
  | .L => .lo
  | .R => .hi

theorem map_BT_side_eq_some (v : Option BT) (σ : Side) : v.map BT.side = some σ ↔ v = some σ.toBT := by
  rcases v with _ | v
  · simp
  · cases v <;> cases σ <;> simp [BT.side, Side.toBT]

theorem map_LR_side_eq_some (v : Option LR) (σ : Side) : v.map LR.side = some σ ↔ v = some σ.toLR := by
  rcases v with _ | v
  · simp
  · cases v <;> cases σ <;> simp [LR.side, Side.toLR]

theorem toBT_injective : Function.Injective Side.toBT := by
  intro a b h; cases a <;> cases b <;> first | rfl | cases h

theorem toLR_injective : Function.Injective Side.toLR := by
  intro a b h; cases a <;> cases b <;> first | rfl | cases h

variable {S : Type} [Fintype S] [DecidableEq S] {C : ContentOps S} {k : ℕ}
  {c : Plane → RTile C k} {τ : ℕ → Bool × Bool}

/-- **Lemma 3.3, horizontal-only sites**: on a free row `y` of a depth-`d` board, a site of the open
strip whose column is not free is not a vertical carrier. -/
theorem board_not_vcarrier (hc : IsRChart C k c) (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ)
    {d : ℕ} (hd : 1 ≤ d) (m₁ m₂ : ℤ) {x y : ℤ}
    (hx1 : frameLo (phaseOffsets (col τ)) d m₁ < x) (hx2 : x < frameHi (phaseOffsets (col τ)) d m₁)
    (hxf : ¬ IsFree (phaseOffsets (col τ)) d m₁ x) (hy : IsFree (phaseOffsets (row τ)) d m₂ y) :
    ¬ (c (x, y)).1.1.IsVCarrier := by
  rintro ⟨hHW, hoS⟩
  obtain ⟨e₀, he₀, he₀d, hin₀⟩ : ∃ e₀, 1 ≤ e₀ ∧ e₀ < d ∧ InFrame (phaseOffsets (col τ)) e₀ x := by
    by_contra hno
    push Not at hno
    exact hxf ⟨hx1, hx2, fun e he hed => hno e he hed⟩
  have hxin : InFrame (phaseOffsets (col τ)) d x := ⟨m₁, hx1.le, hx2.le⟩
  set W : ℤ → Option Side := fun z => ((c (x, z)).1.1.HW).map BT.side with hWdef
  have hWiff : ∀ z σ, (∃ r, PRank (row τ) z r) → (W z = some σ ↔ ∃ e, 1 ≤ e ∧
      ((σ = .lo ∧ IsLeftEnd (phaseOffsets (row τ)) e z) ∨
        (σ = .hi ∧ IsRightEnd (phaseOffsets (row τ)) e z)) ∧
        InFrame (phaseOffsets (col τ)) e x) := by
    rintro z σ ⟨r, hr⟩
    rw [hWdef, map_BT_side_eq_some]
    exact walls_HW_of_rank hτ (x, z) hr σ
  have hrk : ∀ z, InFrame (phaseOffsets (row τ)) d z → ∃ r, PRank (row τ) z r := fun z hz => by
    obtain ⟨r, -, hr⟩ := exists_prank_le_of_inFrame (row τ) hz; exact ⟨r, hr⟩
  have hBot : W (frameLo (phaseOffsets (row τ)) d m₂) = some .lo :=
    (hWiff _ .lo (hrk _ (inFrame_of_isLeftEnd ⟨m₂, rfl⟩))).2 ⟨d, hd, Or.inl ⟨rfl, ⟨m₂, rfl⟩⟩, hxin⟩
  have hTop : W (frameHi (phaseOffsets (row τ)) d m₂) = some .hi :=
    (hWiff _ .hi (hrk _ (inFrame_of_isRightEnd ⟨m₂, rfl⟩))).2 ⟨d, hd, Or.inr ⟨rfl, ⟨m₂, rfl⟩⟩, hxin⟩
  have hm : ∀ z : ℤ, (c (x, z)).1.1.oN = (c (x, z + 1)).1.1.oS := fun z => by
    have h := congrArg (fun t => t.2.1) (hc.matchN (x, z))
    simpa only [Prod.mk_add_mk, add_zero, RVal.cN, RVal.cS] using h
  have hnone : ∀ z, W z = none → (c (x, z)).1.1.oS = (c (x, z)).1.1.oN := fun z h => by
    have h' : (c (x, z)).1.1.HW = none := by simpa [hWdef] using h
    exact (c (x, z)).2.1.2.1.1 h'
  have hwall : ∀ z σ, W z = some σ →
      ((c (x, z)).1.1.oN).1 = σ.toBT ∧ ((c (x, z)).1.1.oS).2 = σ.toBT := fun z σ h => by
    rw [hWdef, map_BT_side_eq_some] at h
    cases σ
    · exact ⟨((c (x, z)).2.1.2.1.2.1 h).2, ((c (x, z)).2.1.2.1.2.1 h).1⟩
    · exact ⟨((c (x, z)).2.1.2.1.2.2 h).2, ((c (x, z)).2.1.2.1.2.2 h).1⟩
  have hyW : W y = none := by simp [hWdef, show (c (x, y)).1.1.HW = none from hHW]
  obtain ⟨ylo, yhi, hl1, hl2, hh1, hh2, hlo, hhi, hgap⟩ :=
    exists_gap W (fun z => (c (x, z)).1.1.oS) (fun z => (c (x, z)).1.1.oN) Side.toBT
      toBT_injective hm hnone hwall (by rw [hBot]; simp) (by rw [hTop]; simp) hy.1 hy.2.1 hyW hoS
  exact laminar_gap (row τ) (fun e => InFrame (phaseOffsets (col τ)) e x) W m₂ hWiff he₀ he₀d
    hin₀ hy hl2 hh1 hlo hhi hgap hl1 hh2

/-- **Lemma 3.3, vertical-only sites**: on a free column `x` of a depth-`d` board, a site of the
open strip whose row is not free is not a horizontal carrier. -/
theorem board_not_hcarrier (hc : IsRChart C k c) (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ)
    {d : ℕ} (hd : 1 ≤ d) (m₁ m₂ : ℤ) {x y : ℤ}
    (hy1 : frameLo (phaseOffsets (row τ)) d m₂ < y) (hy2 : y < frameHi (phaseOffsets (row τ)) d m₂)
    (hyf : ¬ IsFree (phaseOffsets (row τ)) d m₂ y) (hx : IsFree (phaseOffsets (col τ)) d m₁ x) :
    ¬ (c (x, y)).1.1.IsHCarrier := by
  rintro ⟨hVW, hoW⟩
  obtain ⟨e₀, he₀, he₀d, hin₀⟩ : ∃ e₀, 1 ≤ e₀ ∧ e₀ < d ∧ InFrame (phaseOffsets (row τ)) e₀ y := by
    by_contra hno
    push Not at hno
    exact hyf ⟨hy1, hy2, fun e he hed => hno e he hed⟩
  have hyin : InFrame (phaseOffsets (row τ)) d y := ⟨m₂, hy1.le, hy2.le⟩
  set W : ℤ → Option Side := fun z => ((c (z, y)).1.1.VW).map LR.side with hWdef
  have hWiff : ∀ z σ, (∃ r, PRank (col τ) z r) → (W z = some σ ↔ ∃ e, 1 ≤ e ∧
      ((σ = .lo ∧ IsLeftEnd (phaseOffsets (col τ)) e z) ∨
        (σ = .hi ∧ IsRightEnd (phaseOffsets (col τ)) e z)) ∧
        InFrame (phaseOffsets (row τ)) e y) := by
    rintro z σ ⟨r, hr⟩
    rw [hWdef, map_LR_side_eq_some]
    exact walls_VW_of_rank hτ (z, y) hr σ
  have hrk : ∀ z, InFrame (phaseOffsets (col τ)) d z → ∃ r, PRank (col τ) z r := fun z hz => by
    obtain ⟨r, -, hr⟩ := exists_prank_le_of_inFrame (col τ) hz; exact ⟨r, hr⟩
  have hL : W (frameLo (phaseOffsets (col τ)) d m₁) = some .lo :=
    (hWiff _ .lo (hrk _ (inFrame_of_isLeftEnd ⟨m₁, rfl⟩))).2 ⟨d, hd, Or.inl ⟨rfl, ⟨m₁, rfl⟩⟩, hyin⟩
  have hR : W (frameHi (phaseOffsets (col τ)) d m₁) = some .hi :=
    (hWiff _ .hi (hrk _ (inFrame_of_isRightEnd ⟨m₁, rfl⟩))).2 ⟨d, hd, Or.inr ⟨rfl, ⟨m₁, rfl⟩⟩, hyin⟩
  have hm : ∀ z : ℤ, (c (z, y)).1.1.oE = (c (z + 1, y)).1.1.oW := fun z => by
    have h := congrArg (fun t => t.2.1) (hc.matchE (z, y))
    simpa only [Prod.mk_add_mk, add_zero, RVal.cE, RVal.cW] using h
  have hnone : ∀ z, W z = none → (c (z, y)).1.1.oW = (c (z, y)).1.1.oE := fun z h => by
    have h' : (c (z, y)).1.1.VW = none := by simpa [hWdef] using h
    exact (c (z, y)).2.1.1.1 h'
  have hwall : ∀ z σ, W z = some σ →
      ((c (z, y)).1.1.oE).1 = σ.toLR ∧ ((c (z, y)).1.1.oW).2 = σ.toLR := fun z σ h => by
    rw [hWdef, map_LR_side_eq_some] at h
    cases σ
    · exact ⟨((c (z, y)).2.1.1.2.1 h).2, ((c (z, y)).2.1.1.2.1 h).1⟩
    · exact ⟨((c (z, y)).2.1.1.2.2 h).2, ((c (z, y)).2.1.1.2.2 h).1⟩
  have hxW : W x = none := by simp [hWdef, show (c (x, y)).1.1.VW = none from hVW]
  obtain ⟨ylo, yhi, hl1, hl2, hh1, hh2, hlo, hhi, hgap⟩ :=
    exists_gap W (fun z => (c (z, y)).1.1.oW) (fun z => (c (z, y)).1.1.oE) Side.toLR
      toLR_injective hm hnone hwall (by rw [hL]; simp) (by rw [hR]; simp) hx.1 hx.2.1 hxW hoW
  exact laminar_gap (col τ) (fun e => InFrame (phaseOffsets (row τ)) e y) W m₁ hWiff he₀ he₀d
    hin₀ hx hl2 hh1 hlo hhi hgap hl1 hh2

end UND.Chart
