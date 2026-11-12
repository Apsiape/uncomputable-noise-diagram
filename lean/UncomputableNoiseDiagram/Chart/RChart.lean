/-
# Legal charts of `R`: projections, central words, the controller's readings (S7–S8)

Part of nodes S7 and S8 of `BLUEPRINT.md` (Part A.3), NEW. Paper (Section 2.1): "A full legal
chart means an assignment of live letters compatible in all eight Moore directions. Equivalently
it is the `3 × 3` block presentation of an `R`-tiling with one global bit." Section 3.2: "The usual
overlapping-block edge colours recode these finite constraints as a Wang set, retaining the central
tile projections."

* `IsRChart C k c`: `c` is an `R`-tiling (every edge matches in `R`);
* its decorated quarters form a legal decorated chart (`IsRChart.isDTiling`), hence a tiling of
  `𝔸^q` (`IsRChart.isQTiling`);
* **`IsRChart.word_apply`**, `word_eq`: the central word carried by each tile is the word of the
  quarter tiling centred there (the higher-block presentation is faithful);
* **`IsRChart.phase_eq`**: the decoded phase of the tile at `ξ` is the lane phase (9)
  `ξ₂ - τ₂ - 1 (mod B)`, in every phase `τ`; `phase_eq_zero_iff`;
* **`IsRChart.gate_iff`**: at a tile with `End` on a row of finite parent rank, the gate condition
  `End ∧ p = 0` holds iff the depth `d` of that bottom row satisfies `d ≥ k` (FD2).
-/
import UncomputableNoiseDiagram.Chart.Routing

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UND.Chart

open UPD UPD.Scaffold

variable {S : Type} [Fintype S] [DecidableEq S] {C : ContentOps S} {k : ℕ}

/-- An `R`-tiling: every horizontal and vertical edge matches in `R`. -/
def IsRChart (C : ContentOps S) (k : ℕ) (c : Plane → RTile C k) : Prop :=
  LegalOn (TileE C k) (TileN C k) Set.univ c

namespace IsRChart

variable {c : Plane → RTile C k}

theorem tileE (hc : IsRChart C k c) (ξ : Plane) : TileE C k (c ξ) (c (ξ + (1, 0))) :=
  hc.1 ξ (Set.mem_univ _) (Set.mem_univ _)

theorem tileN (hc : IsRChart C k c) (ξ : Plane) : TileN C k (c ξ) (c (ξ + (0, 1))) :=
  hc.2 ξ (Set.mem_univ _) (Set.mem_univ _)

theorem matchE (hc : IsRChart C k c) (ξ : Plane) :
    RVal.MatchE (c ξ).1.1 (c (ξ + (1, 0))).1.1 := (hc.tileE ξ).1

theorem matchN (hc : IsRChart C k c) (ξ : Plane) :
    RVal.MatchN (c ξ).1.1 (c (ξ + (0, 1))).1.1 := (hc.tileN ξ).1

/-- The decorated quarters of an `R`-tiling form a legal decorated chart. -/
theorem isDTiling (hc : IsRChart C k c) : IsDTiling (fun ξ => (c ξ).1.1.q) :=
  ⟨fun ξ _ _ => congrArg Prod.fst (hc.matchE ξ), fun ξ _ _ => congrArg Prod.fst (hc.matchN ξ)⟩

/-- The quarters of an `R`-tiling form a tiling of `𝔸^q`. -/
theorem isQTiling (hc : IsRChart C k c) : IsQTiling (fun ξ => (c ξ).1.1.q.toQ) :=
  isQTiling_toQ hc.isDTiling

theorem mem_box_iff (ρ : ℕ) (a b : ℤ) :
    (a, b) ∈ FNE.box ρ ↔ -(ρ : ℤ) ≤ a ∧ a ≤ ρ ∧ -(ρ : ℤ) ≤ b ∧ b ≤ ρ := by
  simp only [FNE.box, Finset.mem_product, Finset.mem_Icc, and_assoc]

/-- **The central words are the true words**: the word carried by the tile at `ξ` reads the
quarter of the tile at `ξ + w` at the offset `w`. -/
theorem word_apply (hc : IsRChart C k c) (ξ : Plane) (w : ↥(FNE.box (winRad k))) :
    (c ξ).1.2 w = (c (ξ + w.1)).1.1.q.toQ := by
  obtain ⟨⟨a, b⟩, hw⟩ := w
  suffices H : ∀ n : ℕ, ∀ (ξ : Plane) (a b : ℤ) (hw : (a, b) ∈ FNE.box (winRad k)),
      a.natAbs + b.natAbs = n → (c ξ).1.2 ⟨(a, b), hw⟩ = (c (ξ + (a, b))).1.1.q.toQ from
    H _ ξ a b hw rfl
  intro n
  induction n with
  | zero =>
    intro ξ a b hw hn
    obtain ⟨rfl, rfl⟩ : a = 0 ∧ b = 0 := by omega
    have e : (⟨((0 : ℤ), (0 : ℤ)), hw⟩ : ↥(FNE.box (winRad k))) = boxCtr _ := rfl
    rw [e, (c ξ).2.2, Prod.mk_zero_zero, add_zero]
  | succ n ih =>
    intro ξ a b hw hn
    have hb := (mem_box_iff _ a b).1 hw
    rcases lt_trichotomy a 0 with ha | ha | ha
    · -- from the west neighbour
      have hx : (a + 1, b) ∈ FNE.box (winRad k) := (mem_box_iff _ _ _).2 (by omega)
      have h1 := (hc.tileE (ξ - (1, 0))).2.1 ⟨(a + 1, b), hx⟩ ⟨(a, b), hw⟩ (by simp)
      rw [sub_add_cancel] at h1
      rw [← h1, ih (ξ - (1, 0)) (a + 1) b hx (by omega)]
      rw [show (ξ - (1, 0)) + (a + 1, b) = ξ + (a, b) by
        obtain ⟨x, y⟩ := ξ
        simp only [Prod.mk_sub_mk, Prod.mk_add_mk, Prod.mk.injEq]
        constructor <;> ring]
    · subst ha
      rcases lt_trichotomy b 0 with hb' | hb' | hb'
      · have hx : ((0 : ℤ), b + 1) ∈ FNE.box (winRad k) := (mem_box_iff _ _ _).2 (by omega)
        have h1 := (hc.tileN (ξ - (0, 1))).2.1 ⟨(0, b + 1), hx⟩ ⟨(0, b), hw⟩ (by simp)
        rw [sub_add_cancel] at h1
        rw [← h1, ih (ξ - (0, 1)) 0 (b + 1) hx (by omega)]
        rw [show (ξ - (0, 1)) + (0, b + 1) = ξ + (0, b) by
          obtain ⟨x, y⟩ := ξ
          simp only [Prod.mk_sub_mk, Prod.mk_add_mk, Prod.mk.injEq]
          constructor <;> ring]
      · omega
      · have hx : ((0 : ℤ), b - 1) ∈ FNE.box (winRad k) := (mem_box_iff _ _ _).2 (by omega)
        have h1 := (hc.tileN ξ).2.1 ⟨(0, b), hw⟩ ⟨(0, b - 1), hx⟩ (by simp)
        rw [h1, ih (ξ + (0, 1)) 0 (b - 1) hx (by omega)]
        rw [show (ξ + (0, 1)) + (0, b - 1) = ξ + (0, b) by
          obtain ⟨x, y⟩ := ξ
          simp only [Prod.mk_add_mk, Prod.mk.injEq]
          constructor <;> ring]
    · -- from the east neighbour
      have hx : (a - 1, b) ∈ FNE.box (winRad k) := (mem_box_iff _ _ _).2 (by omega)
      have h1 := (hc.tileE ξ).2.1 ⟨(a, b), hw⟩ ⟨(a - 1, b), hx⟩ (by simp)
      rw [h1, ih (ξ + (1, 0)) (a - 1) b hx (by omega)]
      rw [show (ξ + (1, 0)) + (a - 1, b) = ξ + (a, b) by
        obtain ⟨x, y⟩ := ξ
        simp only [Prod.mk_add_mk, Prod.mk.injEq]
        constructor <;> ring]

theorem word_eq (hc : IsRChart C k c) (ξ : Plane) :
    (c ξ).1.2 = wordAt (winRad k) (fun η => (c η).1.1.q.toQ) ξ :=
  funext (hc.word_apply ξ)

/-- **The decoded phase of an `R`-tiling is the lane phase (9)**, in every phase `τ` of its
quarters: `p(ξ) = ξ₂ - τ₂ - 1 (mod B)`. -/
theorem phase_eq (hc : IsRChart C k c) {τ : ℕ → Bool × Bool}
    (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ) (ξ : Plane) :
    (chartData C k).phase (c ξ) = ((ξ.2 - wsum (row τ) (2 * k) - 1 : ℤ) : ZMod (4 ^ k)) := by
  show phaseTable k (c ξ).1.2 = _
  rw [hc.word_eq ξ, phaseTable_wordAt hτ]

theorem phase_eq_zero_iff (hc : IsRChart C k c) {τ : ℕ → Bool × Bool}
    (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ) (ξ : Plane) :
    (chartData C k).phase (c ξ) = 0 ↔ lanePhase (row τ) k ξ.2 = 0 := by
  show phaseTable k (c ξ).1.2 = 0 ↔ _
  rw [hc.word_eq ξ, phaseTable_wordAt_eq_zero_iff hτ]

/-- **The gate on a finite bottom row** (§3.2, FD2): at a tile with `End` whose row has a finite
parent rank, the tile is `(R_d(z), Bot_d(z'))` for one depth `d ≥ 1`, and the decoded phase
vanishes iff `d ≥ k`. -/
theorem gate_iff (hc : IsRChart C k c) {τ : ℕ → Bool × Bool}
    (hτ : IsQPhase (fun η => (c η).1.1.q.toQ) τ) (ξ : Plane) {r : ℕ}
    (hr : PRank (row τ) ξ.2 r) (hE : (chartData C k).endP (c ξ) = true) :
    ∃ d, 1 ≤ d ∧ IsRightEnd (phaseOffsets (col τ)) d ξ.1 ∧
      IsLeftEnd (phaseOffsets (row τ)) d ξ.2 ∧ ((chartData C k).phase (c ξ) = 0 ↔ k ≤ d) := by
  have hE' : IsEnd (c ξ).1.1.q.toQ := of_decide_eq_true hE
  obtain ⟨d, hd, hcol, hrow, hiff⟩ := end_gate hτ ξ hr hE' k
  exact ⟨d, hd, hcol, hrow, (hc.phase_eq_zero_iff hτ ξ).trans hiff⟩

end IsRChart

end UND.Chart
