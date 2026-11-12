/-
# Section 7: the stationary helper initialization and the hybrid trajectory (Mem1, first part)

Part of node Mem1 of `BLUEPRINT.md` (Part A.7), NEW (D42, CONFIRMED by QB, s9).

Paper (Section 7): "Fix a correct cutoff chart from Prop 4.3 and one of its two global bit lifts.
Start data and the second coordinate at that chart, cloned over providers. Initialize each helper
by its ideal chart-driven copying process with independent negative-time noise. Since every point
of a lane has an earlier reset or an earlier replacement almost surely, this stationary
initialization exists." Lemma 7.1 (proof): "Before time zero data drivers may be taken as the
perfect chart for this initialization convention."

Formalization (D42: the initialization is a hybrid trajectory on the two-sided noise):
* `chainSite` (the copy chain `w, w - e_x + v, …`), `ogOf` (the `Orig` bit of a chart symbol);
* `firstHit` (the value at the first hit of a sequence), `firstHit_cons`, `firstHit_map`,
  **`measurableSet_firstHit`** (first-hit functions on sequences of a countable discrete space are
  measurable);
* `initField'` (field `j` at `w` from a past noise `P` and the chart symbols `cS`: the mark at the
  first flag or the reset at the first origin along the copy chain, `{0}` if neither exists, a null
  event for `ε > 0`), `initField`, `initCfg` (data and second coordinate at the chart);
  **`initField_rec`** (the ideal field obeys (4) with the chart's drivers at every time `≤ 0`);
* `encodeConfig`, `posPart`, `negPart`, `X0` (the time-0 configuration from the negative-time
  noise), **`hyb`** (the hybrid trajectory: `initCfg` at times `≤ 0`, the automaton driven by the
  positive-time noise from time `0` on), **`hyb_succ`** (the decoded update at positive times);
* **`hyb_hyp`**: for a full legal chart `ref` with `cS = some ∘ ref`, the hybrid trajectory
  satisfies the hypotheses of Lemma 7.1 for every noise (helpers follow (4) at every integer time,
  data follow the rule at positive times, data are the chart at times `≤ 0`);
* **`measurable_X0`** (the initialization is a measurable function of the chart parameter and the
  negative-time noise, when the chart symbols are), **`X0_shift`** (it is translation covariant).
-/
import UncomputableNoiseDiagram.Memory.Error
import UncomputableNoiseDiagram.PCA.Translation

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory

namespace UND.Memory

open UND.Rule UND.Sensors
open FNE (Plane box)

/- D21: `T = 500` stays opaque. -/
attribute [local irreducible] UND.Param.T

/-! ## First hits -/

section FirstHit

open Classical in
/-- The value at the first hit of a sequence (`dflt` if there is none). -/
def firstHit {X Y : Type*} (hit : X → Prop) (val : ℕ → X → Y) (dflt : Y) (s : ℕ → X) : Y :=
  if h : ∃ m, hit (s m) then val (Nat.find h) (s (Nat.find h)) else dflt

open Classical in
theorem firstHit_cons {X Y : Type*} (hit : X → Prop) (val : ℕ → X → Y) (dflt : Y) (s : ℕ → X) :
    firstHit hit val dflt s = if hit (s 0) then val 0 (s 0)
      else firstHit hit (fun m => val (m + 1)) dflt (fun m => s (m + 1)) := by
  by_cases h0 : hit (s 0)
  · have hex : ∃ m, hit (s m) := ⟨0, h0⟩
    have hf : Nat.find hex = 0 := Nat.find_eq_zero hex |>.2 h0
    rw [ite_eq_left h0]
    unfold firstHit
    rw [dite_eq_left hex]
    simp only [hf]
  · rw [ite_eq_right h0]
    unfold firstHit
    by_cases hex : ∃ m, hit (s m)
    · have hex' : ∃ m, hit (s (m + 1)) := by
        obtain ⟨m, hm⟩ := hex
        cases m with
        | zero => exact absurd hm h0
        | succ m => exact ⟨m, hm⟩
      have hf := Nat.find_comp_succ hex hex' h0
      rw [dite_eq_left hex, dite_eq_left hex']
      simp only [hf]
    · have hex' : ¬ ∃ m, hit (s (m + 1)) := fun ⟨m, hm⟩ => hex ⟨m + 1, hm⟩
      rw [dite_eq_right hex, dite_eq_right hex']

theorem firstHit_map {X Y : Type*} (hit : X → Prop) (val : ℕ → X → Y) (dflt : Y) (g : Y → Y)
    (hv : ∀ m x, g (val m x) = val (m + 1) x) (hd : g dflt = dflt) (s : ℕ → X) :
    g (firstHit hit val dflt s) = firstHit hit (fun m => val (m + 1)) dflt s := by
  classical
  unfold firstHit
  by_cases hex : ∃ m, hit (s m)
  · rw [dite_eq_left hex, dite_eq_left hex, hv]
  · rw [dite_eq_right hex, dite_eq_right hex, hd]

/-- **First-hit functions are measurable** on sequences of a countable discrete space. -/
theorem measurableSet_firstHit {X Y : Type*} [MeasurableSpace X] [MeasurableSingletonClass X]
    [Countable X] (hit : X → Prop) (val : ℕ → X → Y) (dflt : Y) (y : Y) :
    MeasurableSet {s : ℕ → X | firstHit hit val dflt s = y} := by
  classical
  have hcoord : ∀ (m : ℕ) (P : X → Prop), MeasurableSet {s : ℕ → X | P (s m)} :=
    fun m P => (measurable_pi_apply m) (Set.to_countable {x : X | P x}).measurableSet
  have e : {s : ℕ → X | firstHit hit val dflt s = y} =
      (⋃ m : ℕ, ({s : ℕ → X | hit (s m) ∧ val m (s m) = y} ∩
        ⋂ i ∈ Finset.range m, {s : ℕ → X | ¬ hit (s i)})) ∪
      ((⋂ m : ℕ, {s : ℕ → X | ¬ hit (s m)}) ∩ {_s | dflt = y}) := by
    ext s
    simp only [Set.mem_ofPred_eq, Set.mem_union, Set.mem_iUnion, Set.mem_inter_iff,
      Set.mem_iInter, Finset.mem_range]
    unfold firstHit
    by_cases hex : ∃ m, hit (s m)
    · rw [dite_eq_left hex]
      constructor
      · intro h
        exact Or.inl ⟨Nat.find hex, ⟨Nat.find_spec hex, h⟩, fun i hi => Nat.find_min hex hi⟩
      · rintro (⟨m, ⟨hm, hv⟩, hmin⟩ | ⟨hno, -⟩)
        · have hle : Nat.find hex ≤ m := Nat.find_min' hex hm
          have hge : m ≤ Nat.find hex := by
            by_contra hlt
            exact hmin _ (by omega) (Nat.find_spec hex)
          have : Nat.find hex = m := le_antisymm hle hge
          rw [this]
          exact hv
        · exact absurd (Nat.find_spec hex) (hno _)
    · rw [dite_eq_right hex]
      push Not at hex
      constructor
      · intro h
        exact Or.inr ⟨hex, h⟩
      · rintro (⟨m, ⟨hm, -⟩, -⟩ | ⟨-, h⟩)
        · exact absurd hm (hex m)
        · exact h
  rw [e]
  refine MeasurableSet.union (MeasurableSet.iUnion fun m => ?_) ?_
  · refine (hcoord m (fun x => hit x ∧ val m x = y)).inter ?_
    exact MeasurableSet.biInter (Set.to_countable _) fun i _ => hcoord i (fun x => ¬ hit x)
  · refine (MeasurableSet.iInter fun m => hcoord m (fun x => ¬ hit x)).inter ?_
    by_cases h : dflt = y
    · simp [h]
    · simp [h]

end FirstHit

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData B τ}

/-! ## The ideal chart-driven fields -/

/-- The `m`-th site of the copy chain `w, w - e_x + v, w - 2e_x + 2v, …`. -/
def chainSite (w : ISite) (m : ℕ) : ISite := ((w.1.1 - m, w.1.2), w.2 + (m : ℤ) • vP)

theorem chainSite_zero (w : ISite) : chainSite w 0 = w := by
  simp [chainSite]

theorem chainSite_succ (w : ISite) (m : ℕ) : chainSite w (m + 1) = chainSite (w - ex + vS) m := by
  refine Prod.ext (Prod.ext ?_ ?_) (funext fun i => ?_)
  · simp only [chainSite, ex, vS, Prod.fst_add, Prod.fst_sub, Prod.fst_zero]
    push_cast
    ring
  · simp [chainSite, ex, vS]
  · simp only [chainSite, ex, vS, vP, Prod.snd_add, Prod.snd_sub, Pi.add_apply, Pi.sub_apply,
      Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    push_cast
    ring

theorem chainSite_add (w A : ISite) (m : ℕ) : chainSite (w + A) m = chainSite w m + A := by
  refine Prod.ext (Prod.ext ?_ ?_) (funext fun i => ?_)
  · simp only [chainSite, Prod.fst_add]
    ring
  · simp [chainSite]
  · simp only [chainSite, Prod.snd_add, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    ring

/-- The `Orig` bit of a chart symbol (`false` at `⊥`). -/
def ogOf (σ : ChartSym CD.toWangRel) : Bool :=
  match σ with
  | some q => CD.orig (ctr CD.toWangRel q)
  | none => false

/-- The noise atoms read along a copy chain: a flag with its mark, and the base's `Orig` bit. -/
abbrev AtomX (CD : ChartData B τ) := (Bool × Fin (Fintype.card (PhysSym CD))) × Bool

/-- A hit: a flag or an origin. -/
def hitX (x : AtomX CD) : Prop := x.1.1 = true ∨ x.2 = true

/-- The field `j` at a first hit `m`: the mark itself at `m = 0`, its represented interval
later, the reset `{0}` at an origin. -/
def valX (j : Fin B) (m : ℕ) (x : AtomX CD) : Helper :=
  if x.1.1 = true then
    (if m = 0 then (decodeSym x.1.2 : PhysSym CD).2.2 j
      else (Helper.rep ((decodeSym x.1.2 : PhysSym CD).2.2 j)).repr)
  else Ival.zero.repr

/-- The sequence of atoms along the copy chain of field `j` from `w`, for a past noise `P`
(`P m x` = the noise at `m` updates earlier, site `x`) and chart symbols `cS`. -/
def seqOf (cS : Plane → ChartSym CD.toWangRel)
    (P : ℕ → ISite → Bool × Fin (Fintype.card (PhysSym CD))) (j : Fin B) (w : ISite) :
    ℕ → AtomX CD :=
  fun m => (P m (chainSite w m), ogOf (cS (chainSite w m - jy j).1))

/-- The ideal chart-driven field `j` at `w` for a past noise `P`. -/
def initField' (cS : Plane → ChartSym CD.toWangRel)
    (P : ℕ → ISite → Bool × Fin (Fintype.card (PhysSym CD))) (j : Fin B) (w : ISite) : Helper :=
  firstHit hitX (valX j) Ival.zero.repr (seqOf cS P j w)

/-- The past of a two-sided noise at time `t`. -/
def pastOf (ω : PNoise CD) (t : ℤ) : ℕ → ISite → Bool × Fin (Fintype.card (PhysSym CD)) :=
  fun m x => ω (t - m, siteEquiv.symm x)

/-- The ideal chart-driven field `j` at `(t, w)`. -/
def initField (cS : Plane → ChartSym CD.toWangRel) (ω : PNoise CD) (j : Fin B) (t : ℤ)
    (w : ISite) : Helper :=
  initField' cS (pastOf ω t) j w

/-- The configuration at a time `t ≤ 0`: data and second coordinate at the chart (cloned over
`P`), helpers the ideal chart-driven fields. -/
def initCfg (cS : Plane → ChartSym CD.toWangRel) (ω : PNoise CD) (t : ℤ) : PConfig CD :=
  fun w => (cS w.1, cS w.1, fun j => initField cS ω j t w)

theorem valX_succ (j : Fin B) (m : ℕ) (x : AtomX CD) :
    (Helper.rep (valX j m x)).repr = valX j (m + 1) x := by
  unfold valX
  by_cases h : x.1.1 = true
  · simp only [h, ↓reduceIte, Nat.succ_ne_zero]
    by_cases hm : m = 0
    · simp only [hm, ↓reduceIte]
    · simp only [hm, ↓reduceIte, Helper.rep_repr]
  · simp only [h, Bool.false_eq_true, ↓reduceIte, Helper.rep_repr]

/-- **The ideal field obeys (4) with the chart's drivers**: the mark at a flag, the reset `{0}` at
an origin of the base, the copied represented interval otherwise. -/
theorem initField_rec (cS : Plane → ChartSym CD.toWangRel) (ω : PNoise CD) (j : Fin B) (t : ℤ)
    (w : ISite) : initField cS ω j t w =
      if flagAt ω t w = true then (markAt ω t w).2.2 j
      else if ogOf (cS (w - jy j).1) = true then Ival.zero.repr
      else (Helper.rep (initField cS ω j (t - 1) (w - ex + vS))).repr := by
  classical
  unfold initField initField'
  rw [firstHit_cons]
  have hs0 : seqOf cS (pastOf ω t) j w 0 = (ω (t, siteEquiv.symm w), ogOf (cS (w - jy j).1)) := by
    simp [seqOf, pastOf, chainSite_zero]
  have htail : (fun m => seqOf cS (pastOf ω t) j w (m + 1)) =
      seqOf cS (pastOf ω (t - 1)) j (w - ex + vS) := by
    funext m
    simp only [seqOf, pastOf, chainSite_succ]
    congr 3
    push_cast
    ring
  rw [htail, ← firstHit_map hitX (valX j) Ival.zero.repr (fun h => (Helper.rep h).repr)
    (valX_succ j) (by rw [Helper.rep_repr]), hs0]
  by_cases hf : flagAt ω t w = true
  · have hf' : (ω (t, siteEquiv.symm w)).1 = true := hf
    have hhit : hitX (CD := CD) (ω (t, siteEquiv.symm w), ogOf (cS (w - jy j).1)) := Or.inl hf'
    rw [ite_eq_left hhit, ite_eq_left hf]
    simp [valX, hf', markAt]
  · have hf' : (ω (t, siteEquiv.symm w)).1 = false := by simpa [flagAt] using hf
    rw [ite_eq_right hf]
    by_cases ho : ogOf (cS (w - jy j).1) = true
    · have hhit : hitX (CD := CD) (ω (t, siteEquiv.symm w), ogOf (cS (w - jy j).1)) := Or.inr ho
      rw [ite_eq_left hhit, ite_eq_left ho]
      simp [valX, hf']
    · have hhit : ¬ hitX (CD := CD) (ω (t, siteEquiv.symm w), ogOf (cS (w - jy j).1)) := by
        rintro (h | h)
        · rw [hf'] at h; exact absurd h (by simp)
        · exact ho h
      rw [ite_eq_right hhit, ite_eq_right ho]

/-! ## The hybrid trajectory -/

variable (s : ℕ)

/-- Encoding a configuration of `ℤ² × ℤ⁴` as a configuration of the automaton. -/
def encodeConfig (x : PConfig CD) : (ruleCA CD s).Config :=
  fun w6 => Fintype.equivFin (PhysSym CD) (x (siteEquiv w6))

theorem decode_encode (x : PConfig CD) : decodeConfig (encodeConfig s x) = x := by
  funext w
  simp [decodeConfig, encodeConfig]

theorem encode_decode (x : (ruleCA CD s).Config) : encodeConfig s (decodeConfig x) = x := by
  funext w
  simp only [decodeConfig, encodeConfig, AddEquiv.symm_apply_apply]
  exact Equiv.apply_symm_apply _ _

/-- The positive-time noise (`n ↦` time `n + 1`). -/
def posPart (ω : PNoise CD) : (ruleCA CD s).Noise := fun p => ω ((p.1 : ℤ) + 1, p.2)

/-- The negative-time noise (`n ↦` time `-n`). -/
def negPart (ω : PNoise CD) : (ruleCA CD s).Noise := fun p => ω (-(p.1 : ℤ), p.2)

/-- The past read from a one-sided noise (`m ↦` time `-m`). -/
def pastN (a : (ruleCA CD s).Noise) : ℕ → ISite → Bool × Fin (Fintype.card (PhysSym CD)) :=
  fun m x => a (m, siteEquiv.symm x)

/-- **The time-0 configuration** from the chart symbols and the negative-time noise. -/
def X0 (cS : Plane → ChartSym CD.toWangRel) (a : (ruleCA CD s).Noise) : (ruleCA CD s).Config :=
  encodeConfig s fun w => (cS w.1, cS w.1, fun j => initField' cS (pastN s a) j w)

theorem pastOf_zero (ω : PNoise CD) : pastOf ω 0 = pastN s (negPart s ω) := by
  funext m x
  simp [pastOf, pastN, negPart]

theorem X0_eq (cS : Plane → ChartSym CD.toWangRel) (ω : PNoise CD) :
    X0 s cS (negPart s ω) = encodeConfig s (initCfg cS ω 0) := by
  unfold X0 initCfg initField
  rw [pastOf_zero]

/-- **The hybrid trajectory**: the initialization at times `≤ 0`, the automaton driven by the
positive-time noise from time `0` on. -/
def hyb (cS : Plane → ChartSym CD.toWangRel) (ω : PNoise CD) (t : ℤ) : PConfig CD :=
  if t ≤ 0 then initCfg cS ω t
  else decodeConfig ((ruleCA CD s).run (X0 s cS (negPart s ω)) (posPart s ω) t.toNat)

theorem hyb_nonpos (cS : Plane → ChartSym CD.toWangRel) (ω : PNoise CD) {t : ℤ} (ht : t ≤ 0) :
    hyb s cS ω t = initCfg cS ω t := by
  simp [hyb, ht]

theorem hyb_nat (cS : Plane → ChartSym CD.toWangRel) (ω : PNoise CD) (n : ℕ) :
    hyb s cS ω n = decodeConfig ((ruleCA CD s).run (X0 s cS (negPart s ω)) (posPart s ω) n) := by
  cases n with
  | zero =>
    rw [hyb_nonpos s cS ω (by simp)]
    simp only [CA.run, X0_eq, decode_encode, Nat.cast_zero]
  | succ n =>
    have h : ¬ ((n + 1 : ℕ) : ℤ) ≤ 0 := by omega
    simp only [hyb, h, ↓reduceIte, Int.toNat_natCast]

/-- **The decoded update at positive times.** -/
theorem hyb_succ (hB : 1 ≤ B) (cS : Plane → ChartSym CD.toWangRel) (ω : PNoise CD) (n : ℕ) :
    hyb s cS ω ((n : ℤ) + 1) = fun w =>
      if flagAt ω ((n : ℤ) + 1) w = true then markAt ω ((n : ℤ) + 1) w
      else proposal s (hyb s cS ω n) w := by
  rw [show hyb s cS ω ((n : ℤ) + 1) = hyb s cS ω ((n + 1 : ℕ) : ℤ) by push_cast; rfl,
    hyb_nat, hyb_nat]
  have h := update_decode (proposal (CD := CD) s) (nbhdP B) (fun x a => proposal_translate s x a)
    (fun x y w h => proposal_local s hB h) (fun w => ω ((n : ℤ) + 1, w))
    ((ruleCA CD s).run (X0 s cS (negPart s ω)) (posPart s ω) n)
  refine h.trans ?_
  funext w
  rfl

/-- **The hybrid trajectory satisfies the hypotheses of Lemma 7.1** for every noise: for a full
legal chart `ref` with chart symbols `cS = some ∘ ref`. -/
theorem hyb_hyp (hB : 1 ≤ B) {ref : Plane → LiveLetter CD.toWangRel}
    (hfull : IsFullChart CD.toWangRel ref) {cS : Plane → ChartSym CD.toWangRel}
    (hcS : ∀ u, cS u = some (ref u)) (ω : PNoise CD) {tc tr : ℕ → Bool} {k a W : ℕ}
    (hgate : ∀ ξ : Plane, CD.phase (ctr CD.toWangRel (ref ξ)) = 0 →
      CD.endP (ctr CD.toWangRel (ref ξ)) = true → ∃ d, k ≤ d ∧
        UPD.Scaffold.IsLeftEnd (UPD.Scaffold.phaseOffsets tr) d ξ.2 ∧
        UPD.Scaffold.IsRightEnd (UPD.Scaffold.phaseOffsets tc) d ξ.1 ∧
        CD.hrow (ctr CD.toWangRel (ref ξ)) = decide (d < a) ∧
        ∀ i : ℕ, i ≤ UND.Windows.ell d →
          CD.orig (ctr CD.toWangRel (ref (ξ.1 - i, ξ.2))) = decide (i = UND.Windows.ell d))
    (hshort : ∀ d, d < a → UND.Windows.ell d ≤ W) (hlong : ∀ d, a ≤ d → W < UND.Windows.ell d) :
    MCtx.Hyp ⟨hyb s cS ω, ω, ref, W⟩ s tc tr k a := by
  -- the chart data and its drivers
  have hdata : ∀ t : ℤ, t ≤ 0 → dataOf (hyb s cS ω t) = fun w => some (ref w.1) := by
    intro t ht
    funext w
    rw [hyb_nonpos s cS ω ht]
    exact hcS w.1
  have hA : ∀ t : ℤ, t ≤ 0 → ∀ z, drvA (hyb s cS ω t) z = some (ref z.1) := by
    intro t ht z
    unfold drvA
    rw [hdata t ht, FR_cloned CD.toWangRel hfull]
  have hQ : ∀ t : ℤ, t ≤ 0 → ∀ z, drvQ (hyb s cS ω t) z = some (ref z.1) := by
    intro t ht z
    unfold drvQ
    rw [hdata t ht, Function.iterate_fixed (FR_cloned CD.toWangRel hfull)]
    simp [qShift]
  refine ⟨hfull, fun t w => ?_, fun t ht w hf => ?_, fun t ht w => ?_, hgate, hshort, hlong⟩
  · -- the helpers follow (4) at every integer time
    dsimp only
    by_cases ht : t ≤ 0
    · rw [hyb_nonpos s cS ω ht]
      funext j
      simp only [initCfg]
      rw [initField_rec]
      by_cases hf : flagAt ω t w = true
      · simp only [hf, ↓reduceIte]
      · simp only [hf, Bool.false_eq_true, ↓reduceIte]
        show _ = (Jf (hyb s cS ω (t - 1)) j w).repr
        unfold Jf
        rw [hA (t - 1) (by omega), hQ (t - 1) (by omega), hcS]
        simp only [Jof, ogOf, fieldOf]
        rw [hyb_nonpos s cS ω (by omega : t - 1 ≤ 0)]
        simp only [Prod.fst_sub]
        by_cases ho : CD.orig (ctr CD.toWangRel (ref (w.1 - (jy (j : ℕ)).1))) = true <;>
          simp [ho, initCfg]
    · obtain ⟨n, hn⟩ : ∃ n : ℕ, t = (n : ℤ) + 1 := ⟨(t - 1).toNat, by omega⟩
      subst hn
      rw [hyb_succ s hB cS ω n, add_sub_cancel_right]
      by_cases hf : flagAt ω ((n : ℤ) + 1) w = true
      · simp only [hf, ↓reduceIte]
      · simp only [hf, Bool.false_eq_true, ↓reduceIte]
  · dsimp only at hf ⊢
    obtain ⟨n, hn⟩ : ∃ n : ℕ, t = (n : ℤ) + 1 := ⟨(t - 1).toNat, by omega⟩
    subst hn
    rw [hyb_succ s hB cS ω n, add_sub_cancel_right]
    simp only [dataOf, hf, Bool.false_eq_true, ↓reduceIte]
  · dsimp only
    rw [hdata t ht]

end UND.Memory
