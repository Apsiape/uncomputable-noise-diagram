/-
# Section 3.2: the lane-phase decoder (S5)

Node S5 of `BLUEPRINT.md` (Part A.3), NEW (D7). Paper (Section 3.2): "The lane phase is
`p(x, y) = y - τ₂ - 1 (mod B)` (9). It is implemented by a higher-block Wang extension. Here is an
effective construction of its lookup table. For residues modulo `B` encode the quarter offset and
`2k - 1` base substitution digits. … Search for a central radius whose projected fine words for
distinct residues are disjoint … Decode a liftable word by its unique residue and give an
unliftable word a fixed default. Require `p` to agree with that table, to copy horizontally and
increase by one vertically."

D7: the terminating search for a central radius is replaced by the explicit radius
`ρ_{2k} = 2^{2k+1} - 2` of the hard-model core's `UPD.Scaffold.qphase_local` (the residue
`τ mod 2^{2k} = τ mod B` of a tiling of `𝔸^q` is determined by its quarters on `[-ρ_{2k}, ρ_{2k}]²`).
The table is the same: a liftable word is decoded by its unique residue (here by any lift, all
lifts agreeing modulo `B` by `qphase_local`), an unliftable word by the default `0`.

* `winRad k = ρ_{2k}`, `Word ρ` (quarters on the box `[-ρ, ρ]²`), `wordAt ρ Y ξ` (the word of `Y`
  centred at `ξ`), `Liftable`;
* `phaseTable k` (the lookup table `Word ρ_{2k} → ℤ/Bℤ`, `B = 4^k`);
* `exists_qphase_shift`: translates of tilings of `𝔸^q` have quarter phases;
* **`phaseTable_wordAt`**: on every tiling of `𝔸^q` with quarter phase `τ`, in every phase, the
  table reads the lane phase (9): `p(ξ) = ξ₂ - τ₂ - 1 (mod B)`; hence it copies horizontally and
  increases by one vertically (`phaseTable_wordAt_add_e1`, `phaseTable_wordAt_add_e2`), and agrees
  with `lanePhase` (`phaseTable_wordAt_eq_lanePhase`, `phaseTable_wordAt_eq_zero_iff`).
-/
import UncomputableNoiseDiagram.Chart.LanePhase
import FixedNoiseErgodicity.Statements
import UndecidablePhaseDiagram.Scaffold.QuarterPhase
import Mathlib.Data.ZMod.Basic

set_option autoImplicit false

namespace UND.Chart

open UPD UPD.Scaffold

/-- D7: the central radius `ρ_{2k} = 2^{2k+1} - 2` (`B = 4^k = 2^{2k}`). -/
def winRad (k : ℕ) : ℕ := rho (2 * k)

/-- A central word: quarters on the box `[-ρ, ρ]²`. -/
abbrev Word (ρ : ℕ) := ↥(FNE.box ρ) → Quarter

/-- The word of `Y` centred at `ξ`. -/
def wordAt (ρ : ℕ) (Y : Plane → Quarter) (ξ : Plane) : Word ρ := fun w => Y (ξ + w.1)

/-- A liftable word: the central word of a tiling of `𝔸^q` (which has a quarter phase). -/
abbrev Liftable (ρ : ℕ) (w : Word ρ) : Prop :=
  ∃ Y : Plane → Quarter, ∃ τ : ℕ → Bool × Bool, IsQPhase Y τ ∧ wordAt ρ Y 0 = w

/-- The lookup table of the lane phase: a liftable word is decoded by the residue
`-τ'₂ - 1 (mod B)` of a lift with quarter phase `τ'` (all lifts agree modulo `B`), an unliftable
word by the default `0`. -/
noncomputable def phaseTable (k : ℕ) (w : Word (winRad k)) : ZMod (4 ^ k) := by
  classical
  exact if h : Liftable (winRad k) w then
    ((-(wsum (row h.choose_spec.choose) (2 * k)) - 1 : ℤ) : ZMod (4 ^ k)) else 0

/-- Translates of tilings of `𝔸^q` have quarter phases (`scf:quarter`). -/
theorem exists_qphase_shift {Y : Plane → Quarter} {τ : ℕ → Bool × Bool} (h : IsQPhase Y τ)
    (a : Plane) : ∃ τ', IsQPhase (shift a Y) τ' := by
  obtain ⟨f, hf, rfl, -⟩ := h
  rw [shift_qshift]
  obtain ⟨ψ, hψ⟩ := exists_tower_of_tiling
    (hf.shift ((a.1 + bitZ (τ 0).1) / 2, (a.2 + bitZ (τ 0).2) / 2))
  exact ⟨dcons (par (a.1 + bitZ (τ 0).1), par (a.2 + bitZ (τ 0).2)) ψ, _, hf.shift _, rfl, hψ⟩

theorem wordAt_shift (ρ : ℕ) (Y : Plane → Quarter) (ξ : Plane) :
    wordAt ρ (shift (-ξ) Y) 0 = wordAt ρ Y ξ := by
  funext w
  simp only [wordAt, shift, sub_neg_eq_add]
  rw [zero_add, add_comm]

/-- **The decoder reads the lane phase (9)**, in every phase: on a tiling of `𝔸^q` with quarter
phase `τ`, the table at the word centred at `ξ` is `ξ₂ - τ₂ - 1 (mod B)`. -/
theorem phaseTable_wordAt {Y : Plane → Quarter} {τ : ℕ → Bool × Bool} (hY : IsQPhase Y τ)
    (k : ℕ) (ξ : Plane) :
    phaseTable k (wordAt (winRad k) Y ξ) = ((ξ.2 - wsum (row τ) (2 * k) - 1 : ℤ) : ZMod (4 ^ k)) := by
  classical
  obtain ⟨τ', h'⟩ := exists_qphase_shift hY (-ξ)
  have hL : Liftable (winRad k) (wordAt (winRad k) Y ξ) :=
    ⟨_, τ', h', wordAt_shift _ Y ξ⟩
  unfold phaseTable
  simp only [hL, ↓reduceDIte]
  obtain ⟨h'', hw⟩ := hL.choose_spec.choose_spec
  -- the chosen lift agrees with `T_{-ξ} Y` on `[-ρ, ρ]²`, so its phase agrees modulo `2^{2k}`
  have hYY : ∀ x : Plane, |x.1| ≤ rho (2 * k) → |x.2| ≤ rho (2 * k) →
      hL.choose x = shift (-ξ) Y x := by
    intro x hx1 hx2
    have hmem : x ∈ FNE.box (winRad k) := by
      simp only [FNE.box, Finset.mem_product, Finset.mem_Icc, winRad]
      rw [abs_le] at hx1 hx2
      exact ⟨hx1, hx2⟩
    have e := congrFun (hw.trans (wordAt_shift _ Y ξ).symm) ⟨x, hmem⟩
    simpa only [wordAt, zero_add] using e
  have hloc := qphase_local h'' h' (2 * k) hYY
  have hW : wsum (row hL.choose_spec.choose) (2 * k) = wsum (row τ') (2 * k) :=
    wsum_congr fun m hm => by simp only [row, hloc m hm]
  have hsh := (qphase_shift hY (-ξ) h' (2 * k)).2
  rw [hW, ZMod.intCast_eq_intCast_iff_dvd_sub]
  have e4 : ((4 ^ k : ℕ) : ℤ) = 2 ^ (2 * k) := by push_cast; rw [pow_mul]; norm_num
  rw [e4]
  have e : ξ.2 - wsum (row τ) (2 * k) - 1 - (-wsum (row τ') (2 * k) - 1) =
      wsum (row τ') (2 * k) - wsum (row τ) (2 * k) - (-ξ).2 := by
    simp only [Prod.snd_neg]; ring
  rw [e]
  exact hsh

/-- The table agrees with the integer lane phase `lanePhase` of `LanePhase.lean`. -/
theorem phaseTable_wordAt_eq_lanePhase {Y : Plane → Quarter} {τ : ℕ → Bool × Bool}
    (hY : IsQPhase Y τ) (k : ℕ) (ξ : Plane) :
    phaseTable k (wordAt (winRad k) Y ξ) = ((lanePhase (row τ) k ξ.2 : ℤ) : ZMod (4 ^ k)) := by
  rw [phaseTable_wordAt hY, lanePhase]
  have e : ((4 : ℤ) ^ k) = ((4 ^ k : ℕ) : ℤ) := by push_cast; rfl
  rw [e, ZMod.intCast_mod]

/-- The decoded phase vanishes iff the lane phase does. -/
theorem phaseTable_wordAt_eq_zero_iff {Y : Plane → Quarter} {τ : ℕ → Bool × Bool}
    (hY : IsQPhase Y τ) (k : ℕ) (ξ : Plane) :
    phaseTable k (wordAt (winRad k) Y ξ) = 0 ↔ lanePhase (row τ) k ξ.2 = 0 := by
  rw [phaseTable_wordAt_eq_lanePhase hY, ZMod.intCast_zmod_eq_zero_iff_dvd]
  have hpos : (0 : ℤ) < 4 ^ k := by positivity
  have h0 : 0 ≤ lanePhase (row τ) k ξ.2 := Int.emod_nonneg _ hpos.ne'
  have h1 : lanePhase (row τ) k ξ.2 < 4 ^ k := Int.emod_lt_of_pos _ hpos
  have e : ((4 ^ k : ℕ) : ℤ) = 4 ^ k := by push_cast; rfl
  rw [e]
  constructor
  · intro hd
    obtain ⟨c, hc⟩ := hd
    have : c = 0 := by
      by_contra hc0
      rcases lt_or_gt_of_ne hc0 with hlt | hlt
      · nlinarith
      · nlinarith
    rw [hc, this, mul_zero]
  · intro h; rw [h]; exact dvd_zero _

/-- The decoded phase copies horizontally. -/
theorem phaseTable_wordAt_add_e1 {Y : Plane → Quarter} {τ : ℕ → Bool × Bool}
    (hY : IsQPhase Y τ) (k : ℕ) (ξ : Plane) :
    phaseTable k (wordAt (winRad k) Y (ξ + (1, 0))) = phaseTable k (wordAt (winRad k) Y ξ) := by
  rw [phaseTable_wordAt hY, phaseTable_wordAt hY]
  simp

/-- The decoded phase increases by one vertically. -/
theorem phaseTable_wordAt_add_e2 {Y : Plane → Quarter} {τ : ℕ → Bool × Bool}
    (hY : IsQPhase Y τ) (k : ℕ) (ξ : Plane) :
    phaseTable k (wordAt (winRad k) Y (ξ + (0, 1))) = phaseTable k (wordAt (winRad k) Y ξ) + 1 := by
  rw [phaseTable_wordAt hY, phaseTable_wordAt hY]
  simp only [Prod.snd_add]
  push_cast
  ring

end UND.Chart
