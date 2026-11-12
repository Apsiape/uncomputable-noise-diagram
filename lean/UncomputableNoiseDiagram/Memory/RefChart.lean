/-
# The reference chart of Section 7: the live-letter lift and its gates (Mem1, chart part)

Part of node Mem1 of `BLUEPRINT.md` (Part A.7), NEW.

Paper (Section 2.1): "A full legal chart means an assignment of live letters compatible in all
eight Moore directions. Equivalently it is the `3 × 3` block presentation of an `R`-tiling with one
global bit." Section 7: "Fix a correct cutoff chart from Prop 4.3 and one of its two global bit
lifts." Lemma 7.1 (proof): "A correct current `Q_t` can erase only at a genuine gate of the chart.
At a short gate with correct flag one, its true origin lies less than `W` updates earlier. … At a
long gate with correct flag zero, the true origin is outside the recent `W` window."

Formalization:
* `blockAt`, `isLegalBlock_blockAt`; `liftSym c b` (the lift as chart symbols, `⊥` where the block
  is not legal: a total function of the chart), `liftChart` (the lift of a legal chart),
  **`liftSym_eq`**, **`ctr_liftChart`** (the controller reads the chart's tile), **`liftChart_full`**
  (a full legal chart);
* **`leftEnd_back`** (going back `i ≤ ℓ_d` sites from a right endpoint `R_d` of depth `d`, the
  only left endpoint of depth `d` is `L_d`, at `i = ℓ_d`);
* **`chart_gate`**: in the chart of a typical phase (nonhalting cutoff `2a - 2` or `2a - 1`), a
  tile with lane phase zero and `End` is the end `(R_d(z), Bot_d(z'))` of a finite phase-zero gate
  of depth `d ≥ k`, its row flag is `[d < a]`, and on its row the tiles `i ≤ ℓ_d` sites back are
  origins exactly for `i = ℓ_d` (`orig_iff`, `depth_unique`).
-/
import UncomputableNoiseDiagram.Chart.ChartLaw
import UncomputableNoiseDiagram.Chart.TheCA
import UncomputableNoiseDiagram.Sensors.Ownership

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UND.Memory

open UND.Rule UND.Chart UPD UPD.Scaffold
open FNE (box Cell)

variable {S : Type} [Fintype S] [DecidableEq S] {C : ContentOps S} {k : ℕ}

/-- The `3 × 3` block of a chart around `u`. -/
def blockAt (c : Plane → RTile C k) (u : Plane) : Cell → RTile C k := fun w => c (u + w.1)

theorem isLegalBlock_blockAt {c : Plane → RTile C k} (hc : IsRChart C k c) (u : Plane) :
    IsLegalBlock (chartData C k).toWangRel (blockAt c u) := by
  refine ⟨fun w w' h => ?_, fun w w' h => ?_⟩
  · show TileE C k (c (u + w.1)) (c (u + w'.1))
    rw [h, ← add_assoc]
    exact hc.tileE (u + w.1)
  · show TileN C k (c (u + w.1)) (c (u + w'.1))
    rw [h, ← add_assoc]
    exact hc.tileN (u + w.1)

open Classical in
/-- The live-letter lift of a chart with bit `b`, as chart symbols (`⊥` where the block is not
legal). -/
def liftSym (c : Plane → RTile C k) (b : Bool) (u : Plane) :
    ChartSym (chartData C k).toWangRel :=
  if h : IsLegalBlock (chartData C k).toWangRel (blockAt c u) then some (⟨blockAt c u, h⟩, b)
  else none

/-- The live-letter lift of a legal chart with bit `b`. -/
def liftChart {c : Plane → RTile C k} (hc : IsRChart C k c) (b : Bool) :
    Plane → LiveLetter (chartData C k).toWangRel :=
  fun u => (⟨blockAt c u, isLegalBlock_blockAt hc u⟩, b)

theorem liftSym_eq {c : Plane → RTile C k} (hc : IsRChart C k c) (b : Bool) (u : Plane) :
    liftSym c b u = some (liftChart hc b u) := by
  simp [liftSym, isLegalBlock_blockAt hc u, liftChart]

theorem ctr_liftChart {c : Plane → RTile C k} (hc : IsRChart C k c) (b : Bool) (u : Plane) :
    ctr (chartData C k).toWangRel (liftChart hc b u) = c u := by
  show c (u + (0, 0)) = c u
  rw [Prod.mk_zero_zero, add_zero]

/-- **The lift of a legal chart is a full legal chart.** -/
theorem liftChart_full {c : Plane → RTile C k} (hc : IsRChart C k c) (b : Bool) :
    IsFullChart (chartData C k).toWangRel (liftChart hc b) := by
  intro u d _
  refine ⟨rfl, fun w w' h => ?_⟩
  show c (u + w.1) = c (u + d + w'.1)
  rw [h]
  congr 1
  abel

/-- Going back `i ≤ ℓ_d` sites from a right endpoint of depth `d`, the only left endpoint of
depth `d` is reached at `i = ℓ_d`. -/
theorem leftEnd_back {a : ℕ → ℤ} {d : ℕ} {x : ℤ} (hx : IsRightEnd a d x) {i : ℕ}
    (hi : i ≤ UND.Windows.ell d) : IsLeftEnd a d (x - i) ↔ i = UND.Windows.ell d := by
  obtain ⟨m, rfl⟩ := hx
  have hsub := frameHi_sub_frameLo a d m
  constructor
  · rintro ⟨m', hm'⟩
    have h4 : (4 : ℤ) ^ (d + 1) ∣ frameLo a d m' - frameLo a d m :=
      ⟨m' - m, by simp only [frameLo]; ring⟩
    have hlt := UND.Sensors.ell_lt_four_pow d
    have hi' : (i : ℤ) ≤ (UND.Windows.ell d : ℤ) := by exact_mod_cast hi
    have e : frameLo a d m' - frameLo a d m = (UND.Windows.ell d : ℤ) - i := by linarith
    rw [e] at h4
    have h0 := Int.eq_zero_of_abs_lt_dvd h4 (by rw [abs_lt]; constructor <;> linarith)
    have : (i : ℤ) = UND.Windows.ell d := by linarith
    exact_mod_cast this
  · intro h
    refine ⟨m, ?_⟩
    rw [h]
    linarith

/-- **The gates of the reference chart** (Lemma 7.1's "genuine gate"): in the chart of a typical
phase with the nonhalting cutoff, a tile with lane phase zero and `End` ends a finite phase-zero
gate of depth `d ≥ k` (`R_d` on the bottom row `Bot_d`), its row flag is `[d < a]`, and the tiles
`i ≤ ℓ_d` sites back on its row are origins exactly for `i = ℓ_d`. -/
theorem chart_gate {U : Machine} {n0 cut n : ℕ} {τ : ℕ → Bool × Bool} (hτ : Typical τ)
    (hn : 1 ≤ n) (hn0 : 1 ≤ n0) (hU : ¬ U.HaltsOn n)
    (hcut : cut = 2 * (n + n0) - 2 ∨ cut = 2 * (n + n0) - 1) (t0 : RTile (contentP U n0) k)
    (ξ : Plane)
    (hph : (chartData (contentP U n0) k).phase (chartOf U n0 k cut τ t0 ξ) = 0)
    (hend : (chartData (contentP U n0) k).endP (chartOf U n0 k cut τ t0 ξ) = true) :
    ∃ d, k ≤ d ∧ IsLeftEnd (phaseOffsets (row τ)) d ξ.2 ∧
      IsRightEnd (phaseOffsets (col τ)) d ξ.1 ∧
      (chartData (contentP U n0) k).hrow (chartOf U n0 k cut τ t0 ξ) = decide (d < n + n0) ∧
      ∀ i : ℕ, i ≤ UND.Windows.ell d →
        (chartData (contentP U n0) k).orig (chartOf U n0 k cut τ t0 (ξ.1 - i, ξ.2)) =
          decide (i = UND.Windows.ell d) := by
  have hN : NHalt U n0 cut := ⟨n, hn, hn0, hU, hcut⟩
  have hc := chartOf_isRChart hτ hN t0
  have hq := chartOf_phase hτ hN t0
  obtain ⟨r, hr⟩ := exists_prank_of_notInt hτ.2.2.1 ξ.2
  obtain ⟨d, hd, hR, hL, hiff⟩ := hc.gate_iff hq ξ hr hend
  refine ⟨d, hiff.1 hph, hL, hR, ?_, fun i hi => ?_⟩
  · obtain ⟨m, hm⟩ := hL
    have hf := chartOf_bottom_flag hτ t0 hn hn0 hU hcut hd m ξ.1
    rw [← hm] at hf
    exact hf
  · have ho := orig_iff hq (ξ.1 - i, ξ.2) (Or.inr ⟨r, hr⟩)
    show decide (IsOrig (chartOf U n0 k cut τ t0 (ξ.1 - i, ξ.2)).1.1.q.toQ) = _
    refine decide_eq_decide.2 (ho.trans ?_)
    constructor
    · rintro ⟨d', -, hl, hrow⟩
      have hdd := UND.Sensors.depth_unique (row τ) hrow hL
      subst hdd
      exact (leftEnd_back hR hi).1 hl
    · intro h
      exact ⟨d, hd, (leftEnd_back hR hi).2 h, hL⟩

end UND.Memory
