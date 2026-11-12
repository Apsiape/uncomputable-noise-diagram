/-
# Lemma 8.2 (excluding unmarked liveness) (F2)

Node F2 of `BLUEPRINT.md` (Part A.8), NEW.

Paper (Lemma 8.2): "Almost surely every live data or second-coordinate reading in every complete
trajectory lies in the same raw set `𝓜`." Proof: "Otherwise Lemma 5.3 gives a full chart.
Proposition 4.3 gives a wrong critical end `w`. Its planar site is in the ancient union, so an
unmarked live data witness occurs there at some time; a second-coordinate witness supplies a data
witness one update earlier. An unmarked live data root has a checked centre parent outside its sole
possibly marked cluster. Continue such parents indefinitely at the same planar `w`. At a sampled
vertex of this path apply Lemma 8.1. … The geometric tail excludes the infinite path. Fix `φ` for
the whole argument and then take the finite union of these null events over phases. Countability
handles the possible root site, time and provider."

Formalization (generic in the chart data, D13/s9 pattern; the chart enters through an *oracle*:
every full legal chart has a gate of the two critical kinds, which `halting_gate` supplies for the
automaton of Theorem A):
* the intrinsic event of a node at the planar site `u` (`badK`: short at depth `d₀` over `ℓ_{d₀}`
  atoms, long over the recent `W` atoms), its atoms (`atomsK`, disjoint across times), the deep
  roots (`rootK`: Lemma 5.4's query root at lag `ℓ` on the node's base characteristic);
* **`uld_back`**: an unmarked live (data or second-coordinate) reading has an unmarked live
  *data* reading of the same letter one update earlier, at the same planar site;
* **`node_prop`** (Lemma 8.1 + Lemma 5.4 at one vertex): an unmarked live data reading at the
  gate site carries the intrinsic event or a deep contour at a lag `ℓ ≤ W`;
* **`hpath_of_ul`**: in a complete trajectory, an unmarked live reading yields a historical path
  (`HPath`) at the gate site of the coherent chart;
* **`no_ul_generic`** (Lemma 8.2): almost surely no complete trajectory has an unmarked live
  reading, given the oracle, the single-gate bounds `ρ ≤ α⁴`, `ε ≤ γ⁴` and block weights `≤ β < 1`
  (the countable union over the gate site, the kind and the root node; `hpath_null`).
-/
import UncomputableNoiseDiagram.Forget.Miss
import UncomputableNoiseDiagram.Forget.HistBase

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- `DecidableEq (Sym2 (Pt × ℕ))` has instance size 150 (default limit 128)
set_option synthInstance.maxSize 512

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UND.Forget

open UND.Rule UND.Sensors UND.Raw UND.Deep UND.Counting UND.Coh UND.Memory
open FNE (Plane box)

/- D21: `T = 500` stays opaque wherever `F_R^[T]` (the deep driver) appears in goals. -/
attribute [local irreducible] UND.Param.T

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData B τ}

/-- The replacement flags of a noise on `PNoise CD`, as a predicate. -/
def flagE (ω : PNoise CD) : ℤ → ISite → Prop := fun t w => flagAt ω t w = true

/-! ## The events of a node at a planar site -/

/-- The intrinsic event of the node `x = (t, P)` at the planar site `u` (base characteristic
`(u₁ - t, u₂, P + tv)`): long (`< s` lower successes along the recent `W` atoms) for `hb`, short
(`≥ s` upper successes along `ℓ_{d₀}` atoms) otherwise. -/
def badK (CD : ChartData B τ) (s d0 W : ℕ) (u : Plane) (hb : Bool) (x : Node) :
    Set (PNoise CD) :=
  if hb then LongBad CD s (u.1 - x.1) u.2 (x.2 + x.1 • vP) x.1 W
  else ShortBad CD s (u.1 - x.1) u.2 (x.2 + x.1 • vP) x.1 (UND.Windows.ell d0)

/-- The atoms of `badK`. -/
def atomsK (B d0 W : ℕ) (u : Plane) (hb : Bool) (x : Node) : Finset (ℤ × UND.Site 6) :=
  gateAtoms (u.1 - x.1) u.2 (x.2 + x.1 • vP) x.1 B (if hb then W else UND.Windows.ell d0)

/-- Lemma 5.4's root of the deep query at lag `ℓ` on the base characteristic of `x` at `u`. -/
def rootK (u : Plane) (x : Node) (ℓ : ℕ) : Pt × ℕ :=
  qRoot (x.1 - ℓ) (chSite (u.1 - x.1) u.2 (x.2 + x.1 • vP) (x.1 - ℓ))

theorem chSite_node (u : Plane) (x : Node) :
    chSite (u.1 - x.1) u.2 (x.2 + x.1 • vP) x.1 = (u, x.2) := by
  simp only [chSite, sub_add_cancel, add_sub_cancel_right]

theorem detBy_badK (s d0 W : ℕ) (u : Plane) (hb : Bool) (x : Node) :
    DetBy (atomsK B d0 W u hb x) (badK CD s d0 W u hb x) := by
  cases hb
  · exact detBy_shortBad s _ _ _ _ _
  · exact detBy_longBad s _ _ _ _ _

theorem atomsK_disjoint (d0 W : ℕ) (u : Plane) (hb : Bool) (x z : Node) (h : x.1 ≠ z.1) :
    Disjoint (atomsK B d0 W u hb x) (atomsK B d0 W u hb z) := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  simp only [atomsK, mem_gateAtoms] at hp hp'
  obtain ⟨j, -, i, -, rfl⟩ := hp
  obtain ⟨j', -, i', -, h'⟩ := hp'
  have := (laneAtom_inj h').2.1
  exact h (by linarith)

/-! ## One vertex: Lemma 8.1 and Lemma 5.4 -/

/-- An unmarked live reading has an unmarked live **data** reading of the same letter one update
earlier at the same planar site ("a second-coordinate witness supplies a data witness one update
earlier"; "an unmarked live data root has a checked centre parent outside its sole possibly marked
cluster"). -/
theorem uld_back {s : ℕ} {X : ℤ → PConfig CD} {E M : ℤ → ISite → Prop}
    (hX : IsFlagTraj CD s X E) (hM : MClosed E M) {t : ℤ} {u : Plane} {P : Fin 4 → ℤ}
    {a : LiveLetter CD.toWangRel} (h : UL CD X M t (u, P) a) :
    ∃ π : Prov, ¬ M (t - 1) (u, P + provOff π) ∧
      dataOf (X (t - 1)) (u, P + provOff π) = some a := by
  classical
  have hA := h.drvA hX hM
  rw [drvA, FR_eq_some_iff] at hA
  have hQ : UND.Param.h ≤ (Finset.univ.filter fun π : Prov =>
      chk CD.toWangRel (fun v => dataOf (X (t - 1)) (v, P + provOff π)) u = some a).card := hA
  have hm := card_marked_le hM h.1
  have hK : UND.Param.h = 4 * UND.Param.K := rfl
  have hK0 : 0 < UND.Param.K := by norm_num [UND.Param.K]
  obtain ⟨π, hπ1, hπ2⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega :
    (Finset.univ.filter fun π => MarkedAt (M (t - 1)) (u, P) π).card <
      (Finset.univ.filter fun π : Prov =>
        chk CD.toWangRel (fun v => dataOf (X (t - 1)) (v, P + provOff π)) u = some a).card)
  rw [Finset.mem_filter] at hπ1
  have hπ2' : ¬ MarkedAt (M (t - 1)) (u, P) π := fun hc =>
    hπ2 (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc⟩)
  have c1 := hπ1.2
  simp only [chk] at c1
  split_ifs at c1 with k1
  exact ⟨π, fun hc => hπ2' ⟨0, by simp [box], by simpa using hc⟩, c1⟩

/-- The gate oracle: every full legal chart has a planar site read as an `End` with lane phase
zero and row flag `hb`, with origins on its row exactly `ℓ_d` back, `d = d₁` (long) or `d₀`
(short). -/
def GateOracle (CD : ChartData B τ) (d0 d1 : ℕ) : Prop :=
  ∀ c : Plane → LiveLetter CD.toWangRel, IsFullChart CD.toWangRel c →
    ∃ ξ : Plane, ∃ hb : Bool, CD.phase (ctr CD.toWangRel (c ξ)) = 0 ∧
      CD.endP (ctr CD.toWangRel (c ξ)) = true ∧ CD.hrow (ctr CD.toWangRel (c ξ)) = hb ∧
      ∀ i : ℕ, i ≤ UND.Windows.ell (if hb then d1 else d0) →
        CD.orig (ctr CD.toWangRel (c (ξ.1 - i, ξ.2))) =
          decide (i = UND.Windows.ell (if hb then d1 else d0))

/-- **Lemma 8.1 with Lemma 5.4 at one vertex**: in a complete trajectory, relative to a chart
agreeing with every unmarked live reading, an unmarked live data reading at a gate site carries
the gate's intrinsic event or a deep contour at some lag `ℓ ≤ W`. -/
theorem node_prop {s : ℕ} {ω : PNoise CD} {Y : ℤ → PConfig CD}
    (hF : IsFlagTraj CD s Y (flagE ω)) (hY : HelperTraj s Y ω) {d0 d1 W : ℕ}
    (hd0 : UND.Windows.ell d0 ≤ W) (hd1 : W < UND.Windows.ell d1)
    {c : Plane → LiveLetter CD.toWangRel}
    (hc : ∀ t u P a, UL CD Y (marked (flagE ω)) t (u, P) a → c u = a)
    {ξ : Plane} {hb : Bool} (hph : CD.phase (ctr CD.toWangRel (c ξ)) = 0)
    (hend : CD.endP (ctr CD.toWangRel (c ξ)) = true)
    (hrow : CD.hrow (ctr CD.toWangRel (c ξ)) = hb)
    (horig : ∀ i : ℕ, i ≤ UND.Windows.ell (if hb then d1 else d0) →
      CD.orig (ctr CD.toWangRel (c (ξ.1 - i, ξ.2))) =
        decide (i = UND.Windows.ell (if hb then d1 else d0)))
    {t : ℤ} {P : Fin 4 → ℤ} (hm : ¬ marked (flagE ω) t (ξ, P)) {a : LiveLetter CD.toWangRel}
    (hd : dataOf (Y t) (ξ, P) = some a) :
    ω ∈ badK CD s d0 W ξ hb (t, P) ∨ ∃ ℓ, DeepC W (rootK ξ) ω (t, P) ℓ := by
  classical
  have hM := marked_closed (flagE ω)
  have hE : ¬ flagE ω t (ξ, P) := fun hE => hm (hM t _ (Or.inl hE))
  have hprop := hF t (ξ, P) hE
  have h1 : (if Pin s (Y (t - 1)) (ξ, P) then none else drvA (Y (t - 1)) (ξ, P)) = some a := by
    rw [← hd]
    show _ = (Y t (ξ, P)).1
    rw [hprop]
    rfl
  have hnp : ¬ Pin s (Y (t - 1)) (ξ, P) := by
    intro hp
    simp [hp] at h1
  simp only [hnp, ↓reduceIte] at h1
  have hnode := chSite_node ξ (t, P)
  rw [← hnode] at h1 hnp
  have ex : ((ξ.1 - t + t, ξ.2) : Plane) = ξ := by simp
  have ex' : ∀ i : ℕ, ((ξ.1 - t + t - i, ξ.2) : Plane) = (ξ.1 - i, ξ.2) := fun i => by simp
  have hshort : hb = false → UND.Windows.ell (if hb then d1 else d0) ≤ W := by
    intro h; subst h; simpa using hd0
  have hlong : hb = true → W < UND.Windows.ell (if hb then d1 else d0) := by
    intro h; subst h; simpa using hd1
  rcases missed_erasure hY c (c := ξ.1 - t) (y := ξ.2) (Q := P + t • vP) (t := t)
      (d := if hb then d1 else d0) (W := W) (hb := hb) h1 hnp (by rw [ex]; exact hph)
      (by rw [ex]; exact hend) (by rw [ex]; exact hrow)
      (fun i hi => by rw [ex' i]; exact horig i hi) hshort hlong with
    ⟨rfl, hbad⟩ | ⟨rfl, hbad⟩ | ⟨ℓ, hℓ, q, hq, hne⟩
  · left
    simp only [badK, Bool.false_eq_true, ↓reduceIte]
    exact hbad
  · left
    simp only [badK, ↓reduceIte]
    exact hbad
  · right
    obtain ⟨e, Fl, K, h11, he, hflE, htime, hconn, hK, hG, hin⟩ :=
      deep_wrong_lag hc hq hne hℓ
    refine ⟨ℓ, Fl.card, Fl.image fun y => (y, 0), ⟨h11, hℓ, ?_, ?_, ?_⟩, ?_⟩
    · refine Finset.mem_image.mpr ⟨(K, Fl.image fun y => (y, 0)), ?_, rfl⟩
      refine mem_encLe nbrD (36 * UND.Param.q) card_nbrD_le
        ⟨hK.trans he, hG, hconn, fun v hv => ?_⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
      exact Or.inr (hin y hy)
    · exact Finset.card_image_of_injective _ fun y y' h => (Prod.mk.inj h).1
    · intro v hv
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
      obtain ⟨a1, a2⟩ := htime y hy
      refine ⟨rfl, by simp only; omega, ?_⟩
      simp only
      push_cast at a2 ⊢
      omega
    · intro v hv
      obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hv
      exact hflE y hy

/-! ## The historical path of an unmarked live reading -/

/-- **An unmarked live reading yields a historical path** at the gate site of the coherent chart:
the unmarked live data parents at that site, continued indefinitely, each carrying Lemma 8.1's
alternative. -/
theorem hpath_of_ul {s : ℕ} {ω : PNoise CD} {Y : ℤ → PConfig CD}
    (hF : IsFlagTraj CD s Y (flagE ω)) (hY : HelperTraj s Y ω) {d0 d1 W : ℕ}
    (hd0 : UND.Windows.ell d0 ≤ W) (hd1 : W < UND.Windows.ell d1)
    (horacle : GateOracle CD d0 d1)
    (hul : ∃ t w a, UL CD Y (marked (flagE ω)) t w a) :
    ∃ ξ : Plane, ∃ hb : Bool, ∃ x : Node, HPath W (rootK ξ) (badK CD s d0 W ξ hb) ω x := by
  classical
  have hM := marked_closed (flagE ω)
  obtain ⟨c, hcfull, hc⟩ := coherent_chart hF hM hul
  obtain ⟨ξ, hb, hph, hend, hrow, horig⟩ := horacle c hcfull
  obtain ⟨t0, ⟨u0, P0⟩, a0, h0⟩ := hul
  obtain ⟨P1, a1, h1⟩ := coh_cover hF hM h0 (max (ξ.1 - u0.1).natAbs (ξ.2 - u0.2).natAbs) ξ
    (le_max_left _ _) (le_max_right _ _)
  set t1 := t0 - ((max (ξ.1 - u0.1).natAbs (ξ.2 - u0.2).natAbs : ℕ) : ℤ) with ht1
  have hstep : ∀ (t : ℤ) (P : Fin 4 → ℤ),
      UL CD Y (marked (flagE ω)) t (ξ, P) a1 →
      ∃ π : Prov, UL CD Y (marked (flagE ω)) (t - 1) (ξ, P + provOff π) a1 ∧
        dataOf (Y (t - 1)) (ξ, P + provOff π) = some a1 := by
    intro t P h
    obtain ⟨π, hnm, hdat⟩ := uld_back hF hM h
    exact ⟨π, ⟨hnm, Or.inl hdat⟩, hdat⟩
  choose! πf hπf using hstep
  let p : ℕ → Fin 4 → ℤ := fun k => Nat.rec (motive := fun _ => Fin 4 → ℤ)
    (P1 + provOff (πf t1 P1)) (fun k P => P + provOff (πf (t1 - 1 - k) P)) k
  have hinv : ∀ k : ℕ,
      UL CD Y (marked (flagE ω)) (t1 - 1 - k) (ξ, p k) a1 ∧
        dataOf (Y (t1 - 1 - k)) (ξ, p k) = some a1 := by
    intro k
    induction k with
    | zero =>
      have := hπf t1 P1 h1
      rw [show t1 - 1 - ((0 : ℕ) : ℤ) = t1 - 1 by simp]
      exact this
    | succ k ih =>
      have := hπf (t1 - 1 - k) (p k) ih.1
      rwa [show t1 - 1 - (k : ℤ) - 1 = t1 - 1 - ((k + 1 : ℕ) : ℤ) by push_cast; ring] at this
  refine ⟨ξ, hb, (t1 - 1, p 0), p, rfl, fun k => ⟨πf (t1 - 1 - k) (p k), rfl⟩, fun k => ?_⟩
  have hk := hinv k
  exact node_prop hF hY hd0 hd1 hc hph hend hrow horig hk.1.1 hk.2

/-! ## Lemma 8.2 -/

/-- **Lemma 8.2** (excluding unmarked liveness), generic in the chart data: given the gate oracle
with `ℓ_{d₀} ≤ W < ℓ_{d₁}`, single-gate bounds `ρ ≤ α⁴`, `ε ≤ γ⁴` and block weights at most
`β < 1`, almost surely no complete trajectory has an unmarked live data or second-coordinate
reading: every live reading lies in the raw set `𝓜`. -/
theorem no_ul_generic (hB : 1 ≤ B) (s : ℕ) {ε : ℝ} (h0 : 0 < ε) (h1 : ε ≤ 1) {d0 d1 W : ℕ}
    (hd0 : UND.Windows.ell d0 ≤ W) (hd1 : W < UND.Windows.ell d1)
    (horacle : GateOracle CD d0 d1) (ρ α γ β : ℝ≥0∞)
    (hshort : ∀ c y Q t, pLaw (proposal (CD := CD) s) (nbhdP B) ε
      (ShortBad CD s c y Q t (UND.Windows.ell d0)) ≤ ρ)
    (hlong : ∀ c y Q t, pLaw (proposal (CD := CD) s) (nbhdP B) ε (LongBad CD s c y Q t W) ≤ ρ)
    (hρα : ρ ≤ α ^ 4) (heγ : ENNReal.ofReal ε ≤ γ ^ 4)
    (hβ : (UND.Param.q : ℝ≥0∞) * α +
      ∑' f : ℕ, (if 11 ≤ f then (((W + 1) * (4 * (2 * (36 * UND.Param.q) ^ 2) ^ (50 * (f - 1))) *
        (175 * gap W f + 1) ^ 4 : ℕ) : ℝ≥0∞) * γ ^ (3 * f) else 0) ≤ β) (hβ1 : β < 1) :
    ∀ᵐ ω ∂((ruleCA CD s).noiseLaw₂ ε), ∀ X : ℤ → (ruleCA CD s).Config,
      (ruleCA CD s).IsComplete ω X → ∀ t w a,
        ¬ UL CD (fun t => decodeConfig (X t)) (marked (flagsOf (A := ruleCA CD s) ω)) t w a := by
  have hν : IsProbabilityMeasure ((FNE.flagLaw ε).prod (ruleCA CD s).uniformLaw) :=
    isProbabilityMeasure_noiseSite (proposal (CD := CD) s) (nbhdP B) h0.le h1
  have hnull : ∀ z : Plane × Bool × Node, (ruleCA CD s).noiseLaw₂ ε
      {ω | HPath W (rootK z.1) (badK CD s d0 W z.1 z.2.1) ω z.2.2} = 0 := by
    intro z
    refine @hpath_null B τ _ _ CD W (rootK z.1) ((FNE.flagLaw ε).prod (ruleCA CD s).uniformLaw) hν
      (badK CD s d0 W z.1 z.2.1) (atomsK B d0 W z.1 z.2.1)
      (detBy_badK s d0 W z.1 z.2.1) (atomsK_disjoint d0 W z.1 z.2.1) ρ (ENNReal.ofReal ε) α γ
      ?_ ?_ hρα heγ β (fun x => (blk_sum_le W (rootK z.1) α γ x).trans hβ) hβ1 z.2.2
    · intro x
      unfold badK
      cases z.2.1
      · exact hshort _ _ _ _
      · exact hlong _ _ _ _
    · intro S
      exact le_of_eq (flags_measure (caOf (proposal (CD := CD) s) (nbhdP B)) h0.le h1 S)
  rw [ae_iff]
  refine measure_mono_null (fun ω hω => ?_) (measure_iUnion_null hnull)
  simp only [Set.mem_ofPred_eq] at hω
  push Not at hω
  obtain ⟨X, hX, t, w, a, hul⟩ := hω
  obtain ⟨ξ, hb, x, hp⟩ := hpath_of_ul (s := s) (ω := ω) (Y := fun t => decodeConfig (X t))
    (isFlagTraj_of_complete CD s hB hX) (helperTraj_of_complete CD s hB hX) hd0 hd1 horacle
    ⟨t, w, a, hul⟩
  exact Set.mem_iUnion.mpr ⟨(ξ, hb, x), hp⟩

end UND.Forget
