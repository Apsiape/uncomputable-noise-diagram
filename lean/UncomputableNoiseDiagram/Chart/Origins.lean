/-
# Section 3.2: origins and ends (S6); finite ranks in a closed frame (S8, first step of Lemma 3.3)

Nodes S6 and S8 (first step) of `BLUEPRINT.md` (Part A.3), NEW.

Paper (Section 3.2): "Define `Orig` as the intersection of a bottom light horizontal wall with a
left light vertical wall, and `End` with a right light vertical wall. These are literal functions
of a quarter tile's red atoms, quadrant and ruler bits. On a finite bottom row of depth `d`,
origins and ends are respectively `(L_d(z), Bot_d(z'))`, `(R_d(z), Bot_d(z'))`, `ℓ_d = R_d - L_d
= 2·4^d - 1`. Here `Bot_d` denotes the lower endpoint of a row frame. Finite-rank Red paths gives
this assertion even if the other phase coordinate is exceptional. At this row
`p(Bot_d(z')) ≡ (4z'+1)4^d (mod 4^{min(d+1,k)})`, so the phase-zero gates are exactly the finite
bottom rows with `d ≥ k`" (the last clause in the restricted form of FD2).

Lemma 3.3, proof, first paragraph: "Write `z - δ_i = 2u + σ` … Its parent rank is `ν₂(u - ϖ_i)`.
If that rank is at least `2d + 1`, including infinity, then `z - τ_i ≡ σ (mod 4^{d+1})`. Every
coordinate in the closed frame has residue in `[4^d + 1, 3·4^d]`, which contains neither `0` nor
`1`. All coordinates of the closed rectangle therefore have finite parent rank at most `2d`."

* `PRank t z r`: the physical coordinate `z` has parent rank `r` for the phase coordinate with
  binary digits `t` (`t 0 = δ_i`, the tail is `ϖ_i`); it is the hypothesis form of
  `walls_VW_of_rank`, `walls_HW_of_rank`;
* **`exists_prank_le_of_inFrame`** (Lemma 3.3, first step): a coordinate of a closed depth-`d`
  frame has a finite parent rank `≤ 2d`, in every phase;
* `IsOrig`, `IsEnd` (decidable predicates on quarters, read by the controller);
* **`bottom_corner_iff`**, **`orig_iff`**, **`end_iff`**: when one of the two coordinates has a
  finite parent rank (in particular on every finite bottom row), `Orig` holds iff `ξ = (L_d(z),
  Bot_d(z'))` and `End` iff `ξ = (R_d(z), Bot_d(z'))` for one depth `d ≥ 1`;
* **`end_gate`**: at an `End` on a finite bottom row, its depth `d` satisfies `p = 0 ⟺ d ≥ k`
  (FD2, with `lanePhase_bot_eq_zero_iff`).
-/
import UncomputableNoiseDiagram.Chart.Walls
import UncomputableNoiseDiagram.Chart.LanePhase

set_option autoImplicit false

namespace UND.Chart

open UPD UPD.Scaffold

/-- The physical coordinate `z = δ + 2u + σ` has parent rank `r = ν₂(u - ϖ)`, for the phase
coordinate `τ_i` with binary digits `t` (`δ = t 0`, `ϖ` has digits `t (m + 1)`). -/
def PRank (t : ℕ → Bool) (z : ℤ) (r : ℕ) : Prop :=
  IsRank (fun m => t (m + 1)) ((z - bitZ (t 0)) / 2) r

/-- **Lemma 3.3, first step**: every coordinate of a closed frame of depth `d` has a finite parent
rank, at most `2d`, in every phase (including the exceptional ones). -/
theorem exists_prank_le_of_inFrame (t : ℕ → Bool) {d : ℕ} {z : ℤ}
    (hz : InFrame (phaseOffsets t) d z) : ∃ r, r ≤ 2 * d ∧ PRank t z r := by
  classical
  set c : ℕ → Bool := fun m => t (m + 1) with hc
  set u : ℤ := (z - bitZ (t 0)) / 2 with hu
  have hex : ∃ m, m < 2 * d + 1 ∧ dig c m u = true := by
    by_contra hno
    push Not at hno
    have hw : wsum (fun m => dig c m u) (2 * d + 1) = 0 := by
      rw [wsum_congr (b' := fun _ => false) (fun m hm => by simpa using hno m hm), wsum_false]
    have h1 := emod_eq_wsum_dig c (2 * d + 1) u
    rw [hw] at h1
    obtain ⟨q, hq⟩ := Int.dvd_of_emod_eq_zero h1
    have ha : phaseOffsets t d = bitZ (t 0) + 2 * wsum c (2 * d + 1) := rfl
    have hz2 := Int.mul_ediv_add_emod (z - bitZ (t 0)) 2
    have hs0 : 0 ≤ (z - bitZ (t 0)) % 2 := Int.emod_nonneg _ (by norm_num)
    have hs1 : (z - bitZ (t 0)) % 2 < 2 := Int.emod_lt_of_pos _ (by norm_num)
    have e : z - phaseOffsets t d = (z - bitZ (t 0)) % 2 + 4 ^ (d + 1) * q := by
      rw [ha, four_pow_succ]
      linear_combination (-1 : ℤ) * hz2 + 2 * hq
    have h4 : (2 : ℤ) ≤ 4 ^ (d + 1) := by
      have : (4 : ℤ) ≤ 4 ^ (d + 1) := le_self_pow₀ (by norm_num) (by omega)
      linarith
    rw [inFrame_iff, e, Int.add_mul_emod_self_left, Int.emod_eq_of_lt hs0 (by linarith)] at hz
    have : (1 : ℤ) ≤ 4 ^ d := one_le_pow₀ (by norm_num)
    linarith [hz.1]
  obtain ⟨m, hm, hdm⟩ := hex
  have hP : ∃ j, dig c j u = true := ⟨m, hdm⟩
  refine ⟨Nat.find hP, ?_, Nat.find_spec hP, fun j hj => ?_⟩
  · have := Nat.find_min' hP hdm
    omega
  · have := Nat.find_min hP hj
    simpa using this

theorem inFrame_of_isLeftEnd {a : ℕ → ℤ} {d : ℕ} {z : ℤ} (h : IsLeftEnd a d z) : InFrame a d z := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨m, le_rfl, (frameLo_lt_frameHi a d m).le⟩

theorem inFrame_of_isRightEnd {a : ℕ → ℤ} {d : ℕ} {z : ℤ} (h : IsRightEnd a d z) :
    InFrame a d z := by
  obtain ⟨m, rfl⟩ := h
  exact ⟨m, (frameLo_lt_frameHi a d m).le, le_rfl⟩

/-- An endpoint of a depth-`d` frame lying in a depth-`e` frame has `d ≤ e` (strict nesting). -/
theorem le_of_end_inFrame (t : ℕ → Bool) {d e : ℕ} {z : ℤ}
    (hend : IsLeftEnd (phaseOffsets t) d z ∨ IsRightEnd (phaseOffsets t) d z)
    (hin : InFrame (phaseOffsets t) e z) : d ≤ e := by
  by_contra hlt
  push Not at hlt
  rcases hend with ⟨m, rfl⟩ | ⟨m, rfl⟩
  · exact (endpoint_not_inFrame (frameOffsets_phase t) hlt m).1 hin
  · exact (endpoint_not_inFrame (frameOffsets_phase t) hlt m).2 hin

/-! ## `Orig` and `End` -/

/-- §3.2, `Orig`: the quarter lies on a bottom light horizontal wall and on a left light vertical
wall. -/
def IsOrig (q : Quarter) : Prop := q.HW = some BT.B ∧ q.VW = some LR.L

/-- §3.2, `End`: the quarter lies on a bottom light horizontal wall and on a right light vertical
wall. -/
def IsEnd (q : Quarter) : Prop := q.HW = some BT.B ∧ q.VW = some LR.R

instance : DecidablePred IsOrig := fun q => by unfold IsOrig; infer_instance

instance : DecidablePred IsEnd := fun q => by unfold IsEnd; infer_instance

/-- A bottom light horizontal wall meeting a light vertical wall of side `s`, at a site where one
of the two coordinates has a finite parent rank: `ξ₂` is the lower endpoint of a row frame of some
depth `d ≥ 1` and `ξ₁` the left (`s = lo`) or right (`s = hi`) endpoint of a column frame of the
same depth. -/
theorem bottom_corner_iff {Y : Plane → Quarter} {τ : ℕ → Bool × Bool} (hY : IsQPhase Y τ)
    (ξ : Plane) (hfin : (∃ r, PRank (col τ) ξ.1 r) ∨ (∃ r, PRank (row τ) ξ.2 r)) (s : Side) :
    ((Y ξ).HW = some Side.lo.toBT ∧ (Y ξ).VW = some s.toLR) ↔
      ∃ d, 1 ≤ d ∧ ((s = .lo ∧ IsLeftEnd (phaseOffsets (col τ)) d ξ.1) ∨
        (s = .hi ∧ IsRightEnd (phaseOffsets (col τ)) d ξ.1)) ∧
        IsLeftEnd (phaseOffsets (row τ)) d ξ.2 := by
  constructor
  · rintro ⟨hH, hV⟩
    -- both coordinates have finite parent ranks
    have hboth : (∃ r, PRank (col τ) ξ.1 r) ∧ (∃ r, PRank (row τ) ξ.2 r) := by
      rcases hfin with ⟨r, hr⟩ | ⟨r, hr⟩
      · obtain ⟨d, -, -, hin⟩ := (walls_VW_of_rank hY ξ hr s).1 hV
        obtain ⟨r', -, hr'⟩ := exists_prank_le_of_inFrame (row τ) hin
        exact ⟨⟨r, hr⟩, ⟨r', hr'⟩⟩
      · obtain ⟨d, -, -, hin⟩ := (walls_HW_of_rank hY ξ hr Side.lo).1 hH
        obtain ⟨r', -, hr'⟩ := exists_prank_le_of_inFrame (col τ) hin
        exact ⟨⟨r', hr'⟩, ⟨r, hr⟩⟩
    obtain ⟨⟨rc, hrc⟩, ⟨rr, hrr⟩⟩ := hboth
    obtain ⟨d, hd, hendR, hinC⟩ := (walls_HW_of_rank hY ξ hrr Side.lo).1 hH
    obtain ⟨d', hd', hendC, hinR⟩ := (walls_VW_of_rank hY ξ hrc s).1 hV
    have hrow : IsLeftEnd (phaseOffsets (row τ)) d ξ.2 := by
      rcases hendR with ⟨-, h⟩ | ⟨h, -⟩
      · exact h
      · cases h
    have h1 : d ≤ d' := le_of_end_inFrame (row τ) (Or.inl hrow) hinR
    have h2 : d' ≤ d := by
      refine le_of_end_inFrame (col τ) ?_ hinC
      rcases hendC with ⟨-, h⟩ | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
    obtain rfl : d = d' := le_antisymm h1 h2
    exact ⟨d, hd, hendC, hrow⟩
  · rintro ⟨d, hd, hcol, hrow⟩
    have hinC : InFrame (phaseOffsets (col τ)) d ξ.1 := by
      rcases hcol with ⟨-, h⟩ | ⟨-, h⟩
      · exact inFrame_of_isLeftEnd h
      · exact inFrame_of_isRightEnd h
    have hinR : InFrame (phaseOffsets (row τ)) d ξ.2 := inFrame_of_isLeftEnd hrow
    obtain ⟨rc, -, hrc⟩ := exists_prank_le_of_inFrame (col τ) hinC
    obtain ⟨rr, -, hrr⟩ := exists_prank_le_of_inFrame (row τ) hinR
    exact ⟨(walls_HW_of_rank hY ξ hrr Side.lo).2 ⟨d, hd, Or.inl ⟨rfl, hrow⟩, hinC⟩,
      (walls_VW_of_rank hY ξ hrc s).2 ⟨d, hd, hcol, hinR⟩⟩

/-- **§3.2, origins**: where one coordinate has a finite parent rank (in particular on a finite
bottom row), `Orig` holds iff `ξ = (L_d(z), Bot_d(z'))` for some depth `d ≥ 1`. -/
theorem orig_iff {Y : Plane → Quarter} {τ : ℕ → Bool × Bool} (hY : IsQPhase Y τ) (ξ : Plane)
    (hfin : (∃ r, PRank (col τ) ξ.1 r) ∨ (∃ r, PRank (row τ) ξ.2 r)) :
    IsOrig (Y ξ) ↔ ∃ d, 1 ≤ d ∧ IsLeftEnd (phaseOffsets (col τ)) d ξ.1 ∧
      IsLeftEnd (phaseOffsets (row τ)) d ξ.2 := by
  refine (bottom_corner_iff hY ξ hfin Side.lo).trans ?_
  constructor
  · rintro ⟨d, hd, (⟨-, h⟩ | ⟨h, -⟩), hrow⟩
    · exact ⟨d, hd, h, hrow⟩
    · cases h
  · rintro ⟨d, hd, h, hrow⟩
    exact ⟨d, hd, Or.inl ⟨rfl, h⟩, hrow⟩

/-- **§3.2, ends**: where one coordinate has a finite parent rank, `End` holds iff
`ξ = (R_d(z), Bot_d(z'))` for some depth `d ≥ 1`. -/
theorem end_iff {Y : Plane → Quarter} {τ : ℕ → Bool × Bool} (hY : IsQPhase Y τ) (ξ : Plane)
    (hfin : (∃ r, PRank (col τ) ξ.1 r) ∨ (∃ r, PRank (row τ) ξ.2 r)) :
    IsEnd (Y ξ) ↔ ∃ d, 1 ≤ d ∧ IsRightEnd (phaseOffsets (col τ)) d ξ.1 ∧
      IsLeftEnd (phaseOffsets (row τ)) d ξ.2 := by
  refine (bottom_corner_iff hY ξ hfin Side.hi).trans ?_
  constructor
  · rintro ⟨d, hd, (⟨h, -⟩ | ⟨-, h⟩), hrow⟩
    · cases h
    · exact ⟨d, hd, h, hrow⟩
  · rintro ⟨d, hd, h, hrow⟩
    exact ⟨d, hd, Or.inr ⟨rfl, h⟩, hrow⟩

/-- **The gate at an end on a finite bottom row** (§3.2, FD2): an `End` on a row of finite parent
rank is `(R_d(z), Bot_d(z'))` for one depth `d ≥ 1`, and there the lane phase vanishes iff
`d ≥ k`. -/
theorem end_gate {Y : Plane → Quarter} {τ : ℕ → Bool × Bool} (hY : IsQPhase Y τ) (ξ : Plane)
    {r : ℕ} (hr : PRank (row τ) ξ.2 r) (hE : IsEnd (Y ξ)) (k : ℕ) :
    ∃ d, 1 ≤ d ∧ IsRightEnd (phaseOffsets (col τ)) d ξ.1 ∧
      IsLeftEnd (phaseOffsets (row τ)) d ξ.2 ∧ (lanePhase (row τ) k ξ.2 = 0 ↔ k ≤ d) := by
  obtain ⟨d, hd, hcol, hrow⟩ := (end_iff hY ξ (Or.inr ⟨r, hr⟩)).1 hE
  refine ⟨d, hd, hcol, hrow, ?_⟩
  obtain ⟨m, hm⟩ := hrow
  rw [hm]
  exact lanePhase_bot_eq_zero_iff (row τ) k d m

end UND.Chart
