/-
# Section 8.1: the wrong critical gate of every full legal chart (F1, chart part)

Part of node F1 of `BLUEPRINT.md` (Part A.8), NEW.

Paper (Lemma 8.2, proof): "Otherwise Lemma 5.3 gives a full chart. Proposition 4.3 gives a wrong
critical end `w`." Lemma 8.1: "For this fixed instance the finite family of residues
`φ = τ mod 4^{a+1}` in both planar coordinates determines all critical finite origins, ends, their
true rides, and their lane phase."

Formalization (every phase): a full legal chart (live letters compatible in all eight Moore
directions, Lemma 5.3's chart) has central tiles forming an `R`-chart (**`isRChart_ctr`**); its
quarters have a quarter phase (the hard-model core's `exists_qphase`), so Prop 4.3's halting branch
(`chart_wrong_flag`) applies: **`halting_gate`** gives a planar site `ξ` read by the controller as
an `End` with lane phase zero, a row flag `hb` (`false` at depth `a - 1`, `true` at depth `a`), and
the origins on its row `i ≤ ℓ_d` sites back exactly at `i = ℓ_d` (`gate_facts`, as `chart_gate`
of Section 7, in every phase).
-/
import UncomputableNoiseDiagram.Memory.RefChart

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UND.Forget

open UND.Rule UND.Chart UPD UPD.Scaffold
open FNE (box Cell mooreDirs)

variable {S : Type} [Fintype S] [DecidableEq S] {C : ContentOps S} {k : ℕ}

/-- **The central tiles of a full legal chart form an `R`-chart** ("equivalently it is the `3 × 3`
block presentation of an `R`-tiling with one global bit"). -/
theorem isRChart_ctr {c : Plane → LiveLetter (chartData C k).toWangRel}
    (hc : IsFullChart (chartData C k).toWangRel c) :
    IsRChart C k (fun u => ctr (chartData C k).toWangRel (c u)) := by
  refine ⟨fun ξ _ _ => ?_, fun ξ _ _ => ?_⟩
  · have h1 := (hc ξ (1, 0) (by decide)).2 ⟨(1, 0), by decide⟩ ⟨(0, 0), by decide⟩ (by decide)
    have h2 := (c ξ).1.2.1 ⟨(0, 0), by decide⟩ ⟨(1, 0), by decide⟩ (by decide)
    rw [h1] at h2
    exact h2
  · have h1 := (hc ξ (0, 1) (by decide)).2 ⟨(0, 1), by decide⟩ ⟨(0, 0), by decide⟩ (by decide)
    have h2 := (c ξ).1.2.2 ⟨(0, 0), by decide⟩ ⟨(0, 1), by decide⟩ (by decide)
    rw [h1] at h2
    exact h2

/-- **The gate facts at a bottom end** of an `R`-chart (every phase): at an `End` that is a
depth-`d` bottom end with `k ≤ d`, the decoded lane phase is zero, and the tiles `i ≤ ℓ_d` sites
back on its row are origins exactly for `i = ℓ_d`. -/
theorem gate_facts {cR : Plane → RTile C k} (hR : IsRChart C k cR) {τ : ℕ → Bool × Bool}
    (hτ : IsQPhase (fun η => (cR η).1.1.q.toQ) τ) {d : ℕ} (hd : 1 ≤ d) (hkd : k ≤ d)
    {ξ : Plane} (hb : IsBottomEnd τ d ξ) :
    (chartData C k).phase (cR ξ) = 0 ∧
      ∀ i : ℕ, i ≤ UND.Windows.ell d →
        (chartData C k).orig (cR (ξ.1 - i, ξ.2)) = decide (i = UND.Windows.ell d) := by
  refine ⟨bottomEnd_gate hR hτ hb hkd, fun i hi => ?_⟩
  obtain ⟨m, hm⟩ := hb.2
  have hr : PRank (row τ) ξ.2 (2 * d - 1) := by rw [hm]; exact prank_frameLo (row τ) hd m
  have hL : IsLeftEnd (phaseOffsets (row τ)) d ξ.2 := hb.2
  have ho := orig_iff hτ (ξ.1 - i, ξ.2) (Or.inr ⟨_, hr⟩)
  show decide (IsOrig (cR (ξ.1 - i, ξ.2)).1.1.q.toQ) = _
  refine decide_eq_decide.2 (ho.trans ?_)
  constructor
  · rintro ⟨d', -, hl, hrow⟩
    have hdd := UND.Sensors.depth_unique (row τ) hrow hL
    subst hdd
    exact (UND.Memory.leftEnd_back hb.1 hi).1 hl
  · intro h
    exact ⟨d, hd, (UND.Memory.leftEnd_back hb.1 hi).2 h, hL⟩

/-- **The wrong critical gate of every full legal chart** (Prop 4.3, halting branch, as read by the
controller; every phase): if `U` halts on `n ≥ 1` (`n₀ ≥ 1`, `k + 1 ≤ a = n + n₀`), every full
legal chart has a planar site `ξ` whose central tile is an `End` with lane phase zero and row flag
`hb`, either `hb = false` at depth `d = a - 1` or `hb = true` at depth `d = a`, and on whose row
the tiles `i ≤ ℓ_d` sites back are origins exactly for `i = ℓ_d`. -/
theorem halting_gate {U : Machine} {n0 n : ℕ}
    {c : Plane → LiveLetter (chartData (contentP U n0) k).toWangRel}
    (hc : IsFullChart (chartData (contentP U n0) k).toWangRel c) (hn : 1 ≤ n) (hn0 : 1 ≤ n0)
    (hk : k + 1 ≤ n + n0) (hU : U.HaltsOn n) :
    ∃ ξ : Plane, ∃ hb : Bool, ∃ d : ℕ,
      ((hb = false ∧ d = n + n0 - 1) ∨ (hb = true ∧ d = n + n0)) ∧
      (chartData (contentP U n0) k).phase (ctr _ (c ξ)) = 0 ∧
      (chartData (contentP U n0) k).endP (ctr _ (c ξ)) = true ∧
      (chartData (contentP U n0) k).hrow (ctr _ (c ξ)) = hb ∧
      ∀ i : ℕ, i ≤ UND.Windows.ell d →
        (chartData (contentP U n0) k).orig (ctr _ (c (ξ.1 - i, ξ.2))) =
          decide (i = UND.Windows.ell d) := by
  have hR := isRChart_ctr hc
  obtain ⟨τ, hτ⟩ := exists_qphase hR.isQTiling
  rcases chart_wrong_flag hR hτ hn hn0 hU with ⟨ξ, hE, hb, hH⟩ | ⟨ξ, hE, hb, hH⟩
  · obtain ⟨hph, horig⟩ := gate_facts hR hτ (by omega) (by omega) hb
    exact ⟨ξ, false, n + n0 - 1, Or.inl ⟨rfl, rfl⟩, hph, decide_eq_true hE, hH, horig⟩
  · obtain ⟨hph, horig⟩ := gate_facts hR hτ (by omega) (by omega) hb
    exact ⟨ξ, true, n + n0, Or.inr ⟨rfl, rfl⟩, hph, decide_eq_true hE, hH, horig⟩

end UND.Forget
