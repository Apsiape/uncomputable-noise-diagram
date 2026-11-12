/-
# Lemma 3.3 (finite-board forcing in every phase): walls and orientation on free lines (S8)

Part of node S8 of `BLUEPRINT.md` (Part A.3), NEW (ADAPTED in spirit from the hard-model core's
routing along lines, `UPD.BG.Line`, here on a strip bounded by two walls).

Paper (Lemma 3.3, proof, second paragraph): "Fix a free row `y_j`. The only vertical light walls on
`[L_*, R_*] × {y_j}` are its two endpoints. Shallower walls cannot occur because `y_j` lies in no
shallower row frame. Same-depth column frames are disjoint. A deeper endpoint cannot lie in the
shallower frame by strict nesting. Orientation matching across the open strip is constant; the left
wall fixes its minus entry to `L` and the right wall its plus entry to `R`. The strip is therefore
horizontally carried with orientation `(L, R)`." (and the transposed statement for free columns)

Every coordinate of the closed board has a finite parent rank `≤ 2d`
(`exists_prank_le_of_inFrame`, the first paragraph), so the finite-rank wall classification
(`walls_VW_of_rank`, `walls_HW_of_rank`) applies at every site, in every phase.

* `strip_orient`: the one-dimensional orientation argument (generic in the axis);
* `endpoint_lt_of_interior`: an endpoint of a depth-`e` frame strictly inside a depth-`d` frame
  has `e < d`;
* **`board_row_walls`**, **`board_row`**: on a free row of a depth-`d` board, the column endpoints
  `L_*`, `R_*` carry left/right light vertical walls, the open strip carries none, and every site
  of the open strip has orientation `(L, R)` on both horizontal edges (a horizontal carrier);
* **`board_col_walls`**, **`board_col`**: the transposed statements on a free column;
* **`board_active`**: free × free sites of the board are active.
-/
import UncomputableNoiseDiagram.Chart.RChart

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UND.Chart

open UPD UPD.Scaffold

/-- **The orientation argument along one line**: on `[L, R]` with walls of the two sides at the
ends and none in between, orientation pairs that match across edges and agree across wall-free
sites are `(a_L, a_R)` on both edges of every interior site. -/
theorem strip_orient {α β : Type*} (W : ℤ → Option β) (o1 o2 : ℤ → α × α)
    (aL aR : α) (hm : ∀ x, o2 x = o1 (x + 1)) (hnone : ∀ x, W x = none → o1 x = o2 x)
    {L R : ℤ} (hL : (o2 L).1 = aL) (hR : (o1 R).2 = aR)
    (hin : ∀ x, L < x → x < R → W x = none) :
    ∀ x, L < x → x < R → o1 x = (aL, aR) ∧ o2 x = (aL, aR) := by
  -- the first entry from the left wall
  have h1 : ∀ i : ℕ, L + 1 + i ≤ R → (o1 (L + 1 + i)).1 = aL := by
    intro i
    induction i with
    | zero =>
      intro _
      rw [show L + 1 + ((0 : ℕ) : ℤ) = L + 1 by simp, ← hm]
      exact hL
    | succ i ih =>
      intro hi
      have hx := hin (L + 1 + i) (by omega) (by push_cast at hi; omega)
      rw [show L + 1 + ((i + 1 : ℕ) : ℤ) = L + 1 + i + 1 by push_cast; ring, ← hm, ← hnone _ hx]
      exact ih (by push_cast at hi ⊢; omega)
  -- the second entry from the right wall
  have h2 : ∀ i : ℕ, L < R - i → (o1 (R - i)).2 = aR := by
    intro i
    induction i with
    | zero => intro _; simpa using hR
    | succ i ih =>
      intro hi
      have hx := hin (R - (i + 1 : ℕ)) (by omega) (by push_cast; omega)
      rw [hnone _ hx, hm, show R - ((i + 1 : ℕ) : ℤ) + 1 = R - i by push_cast; ring]
      exact ih (by omega)
  intro x hLx hxR
  have e1 := h1 (x - L - 1).toNat (by omega)
  have e2 := h2 (R - x).toNat (by omega)
  rw [show L + 1 + ((x - L - 1).toNat : ℤ) = x by omega] at e1
  rw [show R - ((R - x).toNat : ℤ) = x by omega] at e2
  have ho : o1 x = (aL, aR) := Prod.ext e1 e2
  exact ⟨ho, (hnone x (hin x hLx hxR)) ▸ ho⟩

/-- An endpoint of a depth-`e` frame lying strictly inside a depth-`d` frame has `e < d`
(same-depth frames are disjoint; a deeper endpoint is in no shallower frame). -/
theorem endpoint_lt_of_interior (t : ℕ → Bool) {d e : ℕ} {m : ℤ} {x : ℤ}
    (hend : IsLeftEnd (phaseOffsets t) e x ∨ IsRightEnd (phaseOffsets t) e x)
    (h1 : frameLo (phaseOffsets t) d m < x) (h2 : x < frameHi (phaseOffsets t) d m) : e < d := by
  have hle : e ≤ d := le_of_end_inFrame t hend ⟨m, h1.le, h2.le⟩
  rcases hle.lt_or_eq with h | rfl
  · exact h
  · exfalso
    rcases hend with ⟨m', rfl⟩ | ⟨m', rfl⟩
    · have := frame_window_unique (a := phaseOffsets t) (d := e) (z := frameLo (phaseOffsets t) e m')
        ⟨le_rfl, (frameLo_lt_frameHi _ _ _).le⟩ ⟨h1.le, h2.le⟩
      subst this; exact lt_irrefl _ h1
    · have := frame_window_unique (a := phaseOffsets t) (d := e) (z := frameHi (phaseOffsets t) e m')
        ⟨(frameLo_lt_frameHi _ _ _).le, le_rfl⟩ ⟨h1.le, h2.le⟩
      subst this; exact lt_irrefl _ h2

theorem inFrame_of_isFree {a : ℕ → ℤ} {d : ℕ} {m z : ℤ} (h : IsFree a d m z) : InFrame a d z :=
  ⟨m, h.1.le, h.2.1.le⟩

variable {S : Type} [Fintype S] [DecidableEq S] {C : ContentOps S} {k : ℕ}
  {c : Plane → RTile C k} {τ : ℕ → Bool × Bool}

/-- **Lemma 3.3, free rows, walls**: on a free row `y` of a depth-`d` board, the column endpoints
carry a left and a right light vertical wall, and the open strip carries none. -/
theorem board_row_walls (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ) {d : ℕ} (hd : 1 ≤ d)
    (m₁ m₂ : ℤ) {y : ℤ} (hy : IsFree (phaseOffsets (row τ)) d m₂ y) :
    (c (frameLo (phaseOffsets (col τ)) d m₁, y)).1.1.VW = some .L ∧
      (c (frameHi (phaseOffsets (col τ)) d m₁, y)).1.1.VW = some .R ∧
      ∀ x, frameLo (phaseOffsets (col τ)) d m₁ < x → x < frameHi (phaseOffsets (col τ)) d m₁ →
        (c (x, y)).1.1.VW = none := by
  have hyin : InFrame (phaseOffsets (row τ)) d y := inFrame_of_isFree hy
  refine ⟨?_, ?_, fun x hx1 hx2 => ?_⟩
  · obtain ⟨r, -, hr⟩ := exists_prank_le_of_inFrame (col τ)
      (inFrame_of_isLeftEnd (⟨m₁, rfl⟩ : IsLeftEnd (phaseOffsets (col τ)) d _))
    exact (walls_VW_of_rank hτ (_, y) hr Side.lo).2 ⟨d, hd, Or.inl ⟨rfl, ⟨m₁, rfl⟩⟩, hyin⟩
  · obtain ⟨r, -, hr⟩ := exists_prank_le_of_inFrame (col τ)
      (inFrame_of_isRightEnd (⟨m₁, rfl⟩ : IsRightEnd (phaseOffsets (col τ)) d _))
    exact (walls_VW_of_rank hτ (_, y) hr Side.hi).2 ⟨d, hd, Or.inr ⟨rfl, ⟨m₁, rfl⟩⟩, hyin⟩
  · obtain ⟨r, -, hr⟩ := exists_prank_le_of_inFrame (col τ)
      (⟨m₁, hx1.le, hx2.le⟩ : InFrame (phaseOffsets (col τ)) d x)
    show (c (x, y)).1.1.q.toQ.VW = none
    rcases hv : (c (x, y)).1.1.q.toQ.VW with _ | s
    · rfl
    · exfalso
      have hs : ∃ σ : Side, s = σ.toLR := by
        cases s
        · exact ⟨.lo, rfl⟩
        · exact ⟨.hi, rfl⟩
      obtain ⟨σ, rfl⟩ := hs
      obtain ⟨e, he, hend, hin⟩ := (walls_VW_of_rank hτ (x, y) hr σ).1 hv
      have hend' : IsLeftEnd (phaseOffsets (col τ)) e x ∨ IsRightEnd (phaseOffsets (col τ)) e x :=
        hend.imp And.right And.right
      exact hy.2.2 e he (endpoint_lt_of_interior (col τ) hend' hx1 hx2) hin

/-- **Lemma 3.3, free columns, walls**: on a free column `x` of a depth-`d` board, the row
endpoints carry a bottom and a top light horizontal wall, and the open strip carries none. -/
theorem board_col_walls (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ) {d : ℕ} (hd : 1 ≤ d)
    (m₁ m₂ : ℤ) {x : ℤ} (hx : IsFree (phaseOffsets (col τ)) d m₁ x) :
    (c (x, frameLo (phaseOffsets (row τ)) d m₂)).1.1.HW = some .B ∧
      (c (x, frameHi (phaseOffsets (row τ)) d m₂)).1.1.HW = some .T ∧
      ∀ y, frameLo (phaseOffsets (row τ)) d m₂ < y → y < frameHi (phaseOffsets (row τ)) d m₂ →
        (c (x, y)).1.1.HW = none := by
  have hxin : InFrame (phaseOffsets (col τ)) d x := inFrame_of_isFree hx
  refine ⟨?_, ?_, fun y hy1 hy2 => ?_⟩
  · obtain ⟨r, -, hr⟩ := exists_prank_le_of_inFrame (row τ)
      (inFrame_of_isLeftEnd (⟨m₂, rfl⟩ : IsLeftEnd (phaseOffsets (row τ)) d _))
    exact (walls_HW_of_rank hτ (x, _) hr Side.lo).2 ⟨d, hd, Or.inl ⟨rfl, ⟨m₂, rfl⟩⟩, hxin⟩
  · obtain ⟨r, -, hr⟩ := exists_prank_le_of_inFrame (row τ)
      (inFrame_of_isRightEnd (⟨m₂, rfl⟩ : IsRightEnd (phaseOffsets (row τ)) d _))
    exact (walls_HW_of_rank hτ (x, _) hr Side.hi).2 ⟨d, hd, Or.inr ⟨rfl, ⟨m₂, rfl⟩⟩, hxin⟩
  · obtain ⟨r, -, hr⟩ := exists_prank_le_of_inFrame (row τ)
      (⟨m₂, hy1.le, hy2.le⟩ : InFrame (phaseOffsets (row τ)) d y)
    show (c (x, y)).1.1.q.toQ.HW = none
    rcases hv : (c (x, y)).1.1.q.toQ.HW with _ | s
    · rfl
    · exfalso
      have hs : ∃ σ : Side, s = σ.toBT := by
        cases s
        · exact ⟨.lo, rfl⟩
        · exact ⟨.hi, rfl⟩
      obtain ⟨σ, rfl⟩ := hs
      obtain ⟨e, he, hend, hin⟩ := (walls_HW_of_rank hτ (x, y) hr σ).1 hv
      have hend' : IsLeftEnd (phaseOffsets (row τ)) e y ∨ IsRightEnd (phaseOffsets (row τ)) e y :=
        hend.imp And.right And.right
      exact hx.2.2 e he (endpoint_lt_of_interior (row τ) hend' hy1 hy2) hin

/-- **Lemma 3.3, free rows**: the open strip of a free row of a depth-`d` board is horizontally
carried with orientation `(L, R)` (on both horizontal edges of every site). -/
theorem board_row (hc : IsRChart C k c) (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ) {d : ℕ}
    (hd : 1 ≤ d) (m₁ m₂ : ℤ) {y : ℤ} (hy : IsFree (phaseOffsets (row τ)) d m₂ y) :
    ∀ x, frameLo (phaseOffsets (col τ)) d m₁ < x → x < frameHi (phaseOffsets (col τ)) d m₁ →
      (c (x, y)).1.1.VW = none ∧ (c (x, y)).1.1.oW = (.L, .R) ∧ (c (x, y)).1.1.oE = (.L, .R) := by
  obtain ⟨hL, hR, hin⟩ := board_row_walls hτ hd m₁ m₂ hy
  have hm : ∀ x : ℤ, (c (x, y)).1.1.oE = (c (x + 1, y)).1.1.oW := fun x => by
    have h := congrArg (fun t => t.2.1) (hc.matchE (x, y))
    simpa only [Prod.mk_add_mk, add_zero, RVal.cE, RVal.cW] using h
  have hnone : ∀ x : ℤ, (c (x, y)).1.1.VW = none → (c (x, y)).1.1.oW = (c (x, y)).1.1.oE :=
    fun x h => (c (x, y)).2.1.1.1 h
  have hoL := ((c (frameLo (phaseOffsets (col τ)) d m₁, y)).2.1.1.2.1 hL).2
  have hoR := ((c (frameHi (phaseOffsets (col τ)) d m₁, y)).2.1.1.2.2 hR).1
  have h := strip_orient (fun x => (c (x, y)).1.1.VW) (fun x => (c (x, y)).1.1.oW)
    (fun x => (c (x, y)).1.1.oE) LR.L LR.R hm hnone hoL hoR hin
  exact fun x h1 h2 => ⟨hin x h1 h2, h x h1 h2⟩

/-- **Lemma 3.3, free columns**: the open strip of a free column of a depth-`d` board is vertically
carried with orientation `(B, T)` (on both vertical edges of every site). -/
theorem board_col (hc : IsRChart C k c) (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ) {d : ℕ}
    (hd : 1 ≤ d) (m₁ m₂ : ℤ) {x : ℤ} (hx : IsFree (phaseOffsets (col τ)) d m₁ x) :
    ∀ y, frameLo (phaseOffsets (row τ)) d m₂ < y → y < frameHi (phaseOffsets (row τ)) d m₂ →
      (c (x, y)).1.1.HW = none ∧ (c (x, y)).1.1.oS = (.B, .T) ∧ (c (x, y)).1.1.oN = (.B, .T) := by
  obtain ⟨hB, hT, hin⟩ := board_col_walls hτ hd m₁ m₂ hx
  have hm : ∀ y : ℤ, (c (x, y)).1.1.oN = (c (x, y + 1)).1.1.oS := fun y => by
    have h := congrArg (fun t => t.2.1) (hc.matchN (x, y))
    simpa only [Prod.mk_add_mk, add_zero, RVal.cN, RVal.cS] using h
  have hnone : ∀ y : ℤ, (c (x, y)).1.1.HW = none → (c (x, y)).1.1.oS = (c (x, y)).1.1.oN :=
    fun y h => (c (x, y)).2.1.2.1.1 h
  have hoB := ((c (x, frameLo (phaseOffsets (row τ)) d m₂)).2.1.2.1.2.1 hB).2
  have hoT := ((c (x, frameHi (phaseOffsets (row τ)) d m₂)).2.1.2.1.2.2 hT).1
  have h := strip_orient (fun y => (c (x, y)).1.1.HW) (fun y => (c (x, y)).1.1.oS)
    (fun y => (c (x, y)).1.1.oN) BT.B BT.T hm hnone hoB hoT hin
  exact fun y h1 h2 => ⟨hin y h1 h2, h y h1 h2⟩

/-- **Lemma 3.3, active sites**: the sites of the board `F_d^{(1)} × F_d^{(2)}` (free × free) are
active (horizontal and vertical carriers). -/
theorem board_active (hc : IsRChart C k c) (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ) {d : ℕ}
    (hd : 1 ≤ d) (m₁ m₂ : ℤ) {x y : ℤ} (hx : IsFree (phaseOffsets (col τ)) d m₁ x)
    (hy : IsFree (phaseOffsets (row τ)) d m₂ y) : (c (x, y)).1.1.IsActive := by
  obtain ⟨h1, h2, -⟩ := board_row hc hτ hd m₁ m₂ hy x hx.1 hx.2.1
  obtain ⟨h3, h4, -⟩ := board_col hc hτ hd m₁ m₂ hx y hy.1 hy.2.1
  exact ⟨⟨h1, h2⟩, ⟨h3, h4⟩⟩

end UND.Chart
