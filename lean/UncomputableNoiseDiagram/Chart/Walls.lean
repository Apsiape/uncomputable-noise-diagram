/-
# Section 3.1: light walls at a finite-rank coordinate, in every phase (S1 wiring, S6 arithmetic)

Part of nodes S1 (wiring) and S6 of `BLUEPRINT.md` (Part A.3). ADAPTED from the hard-model core's
`UPD.Scaffold.walls_VW`, `walls_HW` (`UndecidablePhaseDiagram/Scaffold/Walls.lean`), which assume
that the phase coordinate is not an integer (`NotInt`, so that every coordinate has a finite parent
rank). Prop 3.1, last paragraph: "A column of finite parent rank `r` carries light vertical wall
sites only if … The column statement assumes only the column's finite rank. … below we apply the
finite-rank statements within one closed frame." Lemma 3.3 works in every phase, including the
exceptional (integer) ones, so the wall statements are needed under the finite-rank hypothesis on
the one coordinate only:

* **`walls_VW_of_rank`**: for a quarter tiling `Y` with phase `τ` and a site `ξ` whose column has a
  finite parent rank (`IsRank (col ϖ) ((ξ - δ)₁ / 2) r`, `ϖ` the tail of `τ`, `δ = bvec (τ 0)`),
  `Y(ξ)` lies on a light vertical wall as a left (right) side iff `ξ₁` is the left (right) endpoint
  of a depth-`d` column frame (`d ≥ 1`) and `ξ₂` lies in a depth-`d` row frame;
* **`walls_HW_of_rank`**: the horizontal statement;
* `frameHi_sub_frameLo`: `R_d - L_d = ℓ_d = 2·4^d - 1` (Section 3.2, origins and ends).
-/
import UndecidablePhaseDiagram.Scaffold.Walls
import UncomputableNoiseDiagram.Windows

set_option autoImplicit false

namespace UND.Chart

open UPD.Scaffold

/-- **Light vertical walls at a column of finite parent rank, in every phase** (`walls_VW` without
`NotInt`). -/
theorem walls_VW_of_rank {Y : FNE.Plane → Quarter} {τ : ℕ → Bool × Bool} (hY : IsQPhase Y τ)
    (ξ : FNE.Plane) {r : ℕ} (hr : IsRank (col fun m => τ (m + 1)) ((ξ - bvec (τ 0)).1 / 2) r)
    (s : Side) :
    (Y ξ).VW = some s.toLR ↔ ∃ d, 1 ≤ d ∧
      ((s = .lo ∧ IsLeftEnd (phaseOffsets (col τ)) d ξ.1) ∨
        (s = .hi ∧ IsRightEnd (phaseOffsets (col τ)) d ξ.1)) ∧
      InFrame (phaseOffsets (row τ)) d ξ.2 := by
  obtain ⟨f, -, rfl, F, hF, hF0⟩ := hY
  have hw := walls_col (hF.towerRel (r + 2))
    (a := fun d => 2 * wsum (col fun m => τ (m + 1)) (2 * d + 1))
    (a' := fun d => 2 * wsum (row fun m => τ (m + 1)) (2 * d + 1)) (fun d => rfl) (fun d => rfl)
    (ξ := ξ - bvec (τ 0)) hr le_rfl s
  have hV : (qshift (τ 0) f ξ).VW =
      (vWall (quad (ξ - bvec (τ 0))) (F 0 (half (ξ - bvec (τ 0))))).map Side.toLR := by
    rw [hF0]; exact VW_quartering f _
  rw [hV, map_toLR_eq_some, hw, phaseOffsets_eq, phaseOffsets_eq]
  simp only [isLeftEnd_add, isRightEnd_add, inFrame_add]
  rfl

/-- **Light horizontal walls at a row of finite parent rank, in every phase** (`walls_HW` without
`NotInt`). -/
theorem walls_HW_of_rank {Y : FNE.Plane → Quarter} {τ : ℕ → Bool × Bool} (hY : IsQPhase Y τ)
    (ξ : FNE.Plane) {r : ℕ} (hr : IsRank (row fun m => τ (m + 1)) ((ξ - bvec (τ 0)).2 / 2) r)
    (s : Side) :
    (Y ξ).HW = some s.toBT ↔ ∃ d, 1 ≤ d ∧
      ((s = .lo ∧ IsLeftEnd (phaseOffsets (row τ)) d ξ.2) ∨
        (s = .hi ∧ IsRightEnd (phaseOffsets (row τ)) d ξ.2)) ∧
      InFrame (phaseOffsets (col τ)) d ξ.1 := by
  obtain ⟨f, -, rfl, F, hF, hF0⟩ := hY
  have hw := walls_row (hF.towerRel (r + 2))
    (a := fun d => 2 * wsum (col fun m => τ (m + 1)) (2 * d + 1))
    (a' := fun d => 2 * wsum (row fun m => τ (m + 1)) (2 * d + 1)) (fun d => rfl) (fun d => rfl)
    (ξ := ξ - bvec (τ 0)) hr le_rfl s
  have hH : (qshift (τ 0) f ξ).HW =
      (hWall (quad (ξ - bvec (τ 0))) (F 0 (half (ξ - bvec (τ 0))))).map Side.toBT := by
    rw [hF0]; exact HW_quartering f _
  rw [hH, map_toBT_eq_some, hw, phaseOffsets_eq, phaseOffsets_eq]
  simp only [isLeftEnd_add, isRightEnd_add, inFrame_add]
  rfl

/-- Section 3.2: the origin and the end of a depth-`d` board row are `ℓ_d = 2·4^d - 1` apart
(`R_d - L_d`, the frame endpoints (7)). -/
theorem frameHi_sub_frameLo (a : ℕ → ℤ) (d : ℕ) (m : ℤ) :
    frameHi a d m - frameLo a d m = (UND.Windows.ell d : ℤ) := by
  have h1 : 1 ≤ 2 * 4 ^ d := by have := Nat.one_le_pow d 4 (by norm_num); omega
  simp only [frameHi, frameLo, UND.Windows.ell]
  push_cast [Nat.cast_sub h1]
  ring

end UND.Chart
