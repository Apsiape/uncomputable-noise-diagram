/-
# Theorem 7.3 (two stationary laws) (Mem4)

Node Mem4 of `BLUEPRINT.md` (Part A.7), NEW.

Paper (Theorem 7.3): "If `U(n)` does not halt, then for every `ε ∈ I_n` the perturbation has two
distinct spatially translation-invariant stationary laws."
Proof: "Condition on the correct chart. Lemmas 6.3 and 7.2 bound every data or second-coordinate
error, uniformly in time, by `Σ_{g≥1}(K_mem γ)^g < 1/4` … Integrate over the invariant chart/helper
initial law. In the bit-`b` initialization the probability of the live data cylinder with bit `b`
is greater than `3/4` at every site and time. The two bit cylinders are disjoint. … The limits from
bits zero and one are distinct."

Formalization (for the automaton `theCA U` of Theorem 9.3):
* the chart parameter is the Haar phase `τ`, the chart `chartOf … τ` of the nonhalting cutoff
  `2a - 2` (`a = n + n₀`), its bit-`b` lift `cSf b τ = liftSym (chartOf … τ) b`;
  `measurableSet_cSf`, `cSf_shift` (covariance under `τ ↦ τ - a`, Haar-a.e.);
* `memLaw b = initLaw … haar (cSf b) ε` (the initial law of Section 7, D42), translation invariant
  (`initLaw_TI`, QB s9) and a probability measure;
* `hyp_typical` (for a typical phase the hybrid trajectory satisfies the hypotheses of Lemma 7.1
  with the reference chart `liftChart … b`, for every noise);
* **`law_memLaw_le`**: if a measurable set of configurations at time `t` forces a data error at
  the origin (relative to the chart of the phase), its probability is at most
  `S = Σ_{g≥1}(K_mem γ)^g < 1/4` (Fubini over the phase, `mem_bad_le`);
* **`memory_branch`**: the memory clause of `Branches` (two translation-invariant initial laws, the
  bit-1 and bit-0 initializations, with memory between them on the one-site cylinder "live data
  with bit 1", `α = 1/2`); **`theorem_7_3`**: two distinct translation-invariant stationary laws;
* **`theoremA_of_halting`**: Theorem A from the halting branch alone (Lemma 8.4's conclusion).
-/
import UncomputableNoiseDiagram.Memory.InitLaw
import UncomputableNoiseDiagram.Memory.RefChart

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UND.Memory

open UND.Rule UND.Sensors UND.Chart UND.Param UPD UPD.Scaffold
open FNE (box Cell)

/-- The series `S = Σ_{g ≥ 1}(K_mem γ)^g` at the selected parameters. -/
def Smem : ℝ := ∑' g : ℕ, ((Kmem : ℝ) * gammaOf (4 ^ kParam)) ^ (g + 1)

theorem Smem_nonneg : 0 ≤ Smem :=
  tsum_nonneg fun _ => pow_nonneg gamma_facts.2.1 _

theorem Smem_lt : Smem < 1 / 4 := gamma_facts.2.2.2

/-- **A data error bound integrated over the chart parameter** (generic in the chart data and
the lane count): if a measurable set of configurations at time `t` forces a data error at the
origin relative to the reference chart of the parameter, and for almost every parameter a data
error has probability at most `S'`, then the set has probability at most `S'` at time `t` from the
initial law. -/
theorem law_initLaw_le {B : ℕ} {τ' : Type*} [Fintype τ'] [DecidableEq τ']
    {CD : ChartData B τ'} (s : ℕ) {Θ : Type*} [MeasurableSpace Θ] (P : Measure Θ)
    [IsProbabilityMeasure P] (cSf : Θ → Plane → ChartSym CD.toWangRel)
    (hcS : ∀ u σ, MeasurableSet {θ | cSf θ u = σ}) {ε : ℝ} (h0 : 0 ≤ ε) (h1 : ε ≤ 1)
    (good : Θ → Prop) (hgood : ∀ᵐ θ ∂P, good θ)
    (ref : ∀ θ, good θ → Plane → LiveLetter CD.toWangRel) (t : ℕ) (S' : ℝ≥0∞)
    (hbound : ∀ θ (h : good θ), pLaw (proposal (CD := CD) s) (nbhdP B) ε
      {ω | dataOf (hyb s (cSf θ) ω t) 0 ≠ some (ref θ h (0 : ISite).1)} ≤ S')
    (Z : Set (ruleCA CD s).Config) (hZ : MeasurableSet Z)
    (hforce : ∀ θ (h : good θ) (ω : PNoise CD),
      encodeConfig s (hyb s (cSf θ) ω t) ∈ Z →
      dataOf (hyb s (cSf θ) ω t) 0 ≠ some (ref θ h (0 : ISite).1)) :
    (ruleCA CD s).law ε (initLaw s P cSf ε) t Z ≤ S' := by
  have := (ruleCA CD s).isProbabilityMeasure_noiseLaw₂ h0 h1
  have hX := measurable_X0 s cSf hcS
  have hHm : Measurable (fun p : Θ × (ruleCA CD s).Noise₂ =>
      (ruleCA CD s).run (X0 s (cSf p.1) (negPart s p.2)) (posPart s p.2) t) :=
    ((ruleCA CD s).measurable_run t).comp (Measurable.prodMk (hX.comp (measurable_fst.prodMk
      ((measurable_negPart s).comp measurable_snd)))
      ((measurable_posPart s).comp measurable_snd))
  rw [law_initLaw s P cSf hcS h0 h1 t, Measure.map_apply hHm hZ, Measure.prod_apply (hHm hZ)]
  have hle : ∀ᵐ θ ∂P, (ruleCA CD s).noiseLaw₂ ε (Prod.mk θ ⁻¹'
      ((fun p : Θ × (ruleCA CD s).Noise₂ => (ruleCA CD s).run
        (X0 s (cSf p.1) (negPart s p.2)) (posPart s p.2) t) ⁻¹' Z)) ≤ S' := by
    filter_upwards [hgood] with θ hθ
    refine le_trans (measure_mono fun ω hω => ?_) (hbound θ hθ)
    have hω2 : (ruleCA CD s).run (X0 s (cSf θ) (negPart s ω)) (posPart s ω) t ∈ Z := hω
    have hω' : encodeConfig s (hyb s (cSf θ) ω t) ∈ Z :=
      (congrArg (fun x => x ∈ Z) (encode_hyb s (cSf θ) ω t)).mpr hω2
    exact hforce θ hθ ω hω'
  calc _ ≤ ∫⁻ _θ, S' ∂P := lintegral_mono_ae hle
    _ = S' := by
        rw [lintegral_const, measure_univ, mul_one]

section Chart

variable (U : Machine) (n : ℕ)

/-- The nonhalting cutoff `2a - 2`, `a = n + n₀`. -/
def cutOf : ℕ := 2 * (n + n0Param) - 2

theorem one_le_n0 : 1 ≤ n0Param := by
  have := n0Param_ge
  omega

variable {U n}

theorem nhalt_cutOf (hn : 1 ≤ n) (hU : ¬ U.HaltsOn n) : NHalt U n0Param (cutOf n) :=
  ⟨n, hn, one_le_n0, hU, Or.inl rfl⟩

open Classical in
/-- The lift of a `3 × 3` block with bit `b`, as a chart symbol. -/
def liftB {S : Type} [Fintype S] [DecidableEq S] {C : ContentOps S} {k : ℕ} (b : Bool)
    (β : Cell → RTile C k) : ChartSym (chartData C k).toWangRel :=
  if h : IsLegalBlock (chartData C k).toWangRel β then some (⟨β, h⟩, b) else none

theorem liftSym_eq_liftB {S : Type} [Fintype S] [DecidableEq S] {C : ContentOps S} {k : ℕ}
    (c : Plane → RTile C k) (b : Bool) (u : Plane) : liftSym c b u = liftB b (blockAt c u) := rfl

/-- The chart symbols of the bit-`b` lift of the chart of phase `τ`. -/
def cSf (t0 : RTile (contentP U n0Param) kParam) (b : Bool) (τ : ℕ → Bool × Bool) :
    Plane → ChartSym (chartData (contentP U n0Param) kParam).toWangRel :=
  liftSym (chartOf U n0Param kParam (cutOf n) τ t0) b

theorem measurableSet_cSf (t0 : RTile (contentP U n0Param) kParam) (b : Bool) (u : Plane)
    (σ : ChartSym (chartData (contentP U n0Param) kParam).toWangRel) :
    MeasurableSet {τ | cSf (n := n) t0 b τ u = σ} := by
  have hm : Measurable fun τ : ℕ → Bool × Bool =>
      blockAt (chartOf U n0Param kParam (cutOf n) τ t0) u :=
    measurable_pi_iff.mpr fun w => (measurable_pi_apply (u + w.1)).comp (measurable_chartOf t0)
  have e : {τ | cSf (n := n) t0 b τ u = σ} =
      (fun τ : ℕ → Bool × Bool => blockAt (chartOf U n0Param kParam (cutOf n) τ t0) u) ⁻¹'
        {β | liftB b β = σ} := by
    ext τ
    simp only [Set.mem_ofPred_eq, Set.mem_preimage]
    rfl
  rw [e]
  exact hm (Set.to_countable _).measurableSet

theorem cSf_shift (t0 : RTile (contentP U n0Param) kParam) (b : Bool) (A : Plane) :
    ∀ᵐ τ ∂haar, ∀ u, cSf (n := n) t0 b τ (u + A) = cSf (n := n) t0 b (addDig (-A) τ) u := by
  filter_upwards [BG.ae_typical_addDig (-A)] with τ h u
  have hsh := chartOf_shift (U := U) (n0 := n0Param) (k := kParam) (cut := cutOf n) h.1.1 h.2.1 t0
  unfold cSf
  rw [liftSym_eq_liftB, liftSym_eq_liftB, hsh]
  congr 1
  funext w
  show chartOf U n0Param kParam (cutOf n) τ t0 (u + A + w.1) =
    chartOf U n0Param kParam (cutOf n) τ t0 (u + w.1 - -A)
  congr 1
  abel

end Chart

variable {U : Machine} {n : ℕ}

/-- **The initial law of Section 7** for bit `b` (D42). -/
def memLaw (t0 : RTile (contentP U n0Param) kParam) (b : Bool) (ε : ℝ) :
    Measure (ruleCA (chartData (contentP U n0Param) kParam) sParam).Config :=
  initLaw sParam haar (cSf (n := n) t0 b) ε

theorem memLaw_prob (t0 : RTile (contentP U n0Param) kParam) (b : Bool) {ε : ℝ} (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) : IsProbabilityMeasure (memLaw (n := n) t0 b ε) :=
  isProbabilityMeasure_initLaw sParam haar _ (measurableSet_cSf t0 b) h0 h1

/-- **The initial law is translation invariant** (QB s9). -/
theorem memLaw_TI (t0 : RTile (contentP U n0Param) kParam) (b : Bool) {ε : ℝ} (h0 : 0 ≤ ε)
    (h1 : ε ≤ 1) :
    (ruleCA (chartData (contentP U n0Param) kParam) sParam).IsTranslationInvariant
      (memLaw (n := n) t0 b ε) := by
  refine initLaw_TI sParam haar _ (measurableSet_cSf t0 b) h0 h1 fun a6 => ?_
  exact ⟨addDig (-(siteEquiv a6).1), measurable_addDig _, haar_map_addDig _,
    cSf_shift t0 b (siteEquiv a6).1⟩

/-- For a typical phase the hybrid trajectory satisfies the hypotheses of Lemma 7.1 for every
noise, with the reference chart the bit-`b` lift of the chart of the phase. -/
theorem hyp_typical (hn : 1 ≤ n) (hU : ¬ U.HaltsOn n) {ε : ℝ}
    (hε : ε ∈ UND.window loF hiF n) (t0 : RTile (contentP U n0Param) kParam) (b : Bool)
    {τ : ℕ → Bool × Bool} (hτ : Typical τ) (ω : PNoise (chartData (contentP U n0Param) kParam)) :
    MCtx.Hyp ⟨hyb sParam (cSf (n := n) t0 b τ) ω, ω,
      liftChart (chartOf_isRChart hτ (nhalt_cutOf hn hU) t0) b, ⌊(C : ℝ) / ε⌋₊⟩
      sParam (col τ) (row τ) kParam (n + n0Param) := by
  have hN := nhalt_cutOf hn hU
  have hc := chartOf_isRChart hτ hN t0
  have hR := regime_final hn hε
  have hB : 1 ≤ 4 ^ kParam := Nat.one_le_pow _ _ (by norm_num)
  refine hyb_hyp sParam hB (liftChart_full hc b) (liftSym_eq hc b) ω ?_ (fun d hd => hR.ell_le hd)
    (fun d hd => ?_)
  · intro ξ hph hend
    rw [ctr_liftChart] at hph hend ⊢
    obtain ⟨d, hkd, hL, hRe, hrow, horig⟩ :=
      chart_gate hτ hn one_le_n0 hU (Or.inl rfl) t0 ξ hph hend
    refine ⟨d, hkd, hL, hRe, hrow, fun i hi => ?_⟩
    rw [ctr_liftChart]
    exact horig i hi
  · have h1 := hR.W_le
    have h2 := UND.Sensors.ell_mono hd
    have hW : 1 ≤ ⌊(C : ℝ) / ε⌋₊ := by
      have h3 := hR.epsW_ge
      have h4 := hR.C_pos
      by_contra h0
      have hW0 : ⌊(C : ℝ) / ε⌋₊ = 0 := by omega
      rw [hW0] at h3
      simp at h3
      linarith
    omega

/-- **The data error bound integrated over the phase** (Theorem 7.3, first paragraph): a
measurable set of configurations at time `t` that forces a data error at the origin, relative to
the chart of the phase, has probability at most `S < 1/4` under the law at time `t` of the bit-`b`
initialization. -/
theorem law_memLaw_le (hn : 1 ≤ n) (hU : ¬ U.HaltsOn n) {ε : ℝ}
    (hε : ε ∈ UND.window loF hiF n) (t0 : RTile (contentP U n0Param) kParam) (b : Bool)
    (t : ℕ) (Z : Set (ruleCA (chartData (contentP U n0Param) kParam) sParam).Config)
    (hZ : MeasurableSet Z)
    (hforce : ∀ τ (hτ : Typical τ) (ω : PNoise (chartData (contentP U n0Param) kParam)),
      encodeConfig sParam (hyb sParam (cSf (n := n) t0 b τ) ω t) ∈ Z →
      dataOf (hyb sParam (cSf (n := n) t0 b τ) ω t) 0 ≠
        some (liftChart (chartOf_isRChart hτ (nhalt_cutOf hn hU) t0) b (0 : ISite).1)) :
    (ruleCA (chartData (contentP U n0Param) kParam) sParam).law ε (memLaw (n := n) t0 b ε) t Z ≤
      ENNReal.ofReal Smem := by
  have hR := regime_final hn hε
  exact law_initLaw_le sParam haar (cSf (n := n) t0 b)
    (measurableSet_cSf t0 b) hR.eps_nonneg hR.eps_le Typical ae_typical
    (fun τ h => liftChart (chartOf_isRChart h (nhalt_cutOf hn hU) t0) b) t _
    (fun τ h => mem_bad_le (proposal (CD := chartData (contentP U n0Param) kParam) sParam)
      (nbhdP (4 ^ kParam)) hn hε (col τ) (row τ)
      (fun ω => hyb sParam (cSf (n := n) t0 b τ) ω)
      (liftChart (chartOf_isRChart h (nhalt_cutOf hn hU) t0) b)
      (fun ω => hyp_typical hn hU hε t0 b h ω) 0 t) Z hZ hforce

/-! ## The memory branch -/

/-- The window `{0}` and the cylinder "live data with bit `1`" at the origin. -/
def win0 : Finset (UND.Site 6) := {0}

theorem zero_mem_win0 : (0 : UND.Site 6) ∈ win0 := Finset.mem_singleton_self 0

/-- Live data with bit `1` at the origin. -/
def liveOne (U : Machine) :
    Set (win0 → (ruleCA (chartData (contentP U n0Param) kParam) sParam).Sym) :=
  {σ | ∃ L, (decodeSym (σ ⟨0, zero_mem_win0⟩) :
    PhysSym (chartData (contentP U n0Param) kParam)).1 = some L ∧ L.2 = true}

theorem mem_cyl_liveOne (cS : Plane → ChartSym (chartData (contentP U n0Param) kParam).toWangRel)
    (ω : PNoise (chartData (contentP U n0Param) kParam)) (t : ℕ) :
    encodeConfig sParam (hyb sParam cS ω t) ∈
        (ruleCA (chartData (contentP U n0Param) kParam) sParam).cyl win0 (liveOne U) ↔
      ∃ L, dataOf (hyb sParam cS ω t) 0 = some L ∧ L.2 = true := by
  show (∃ L, (decodeSym (encodeConfig sParam (hyb sParam cS ω t) 0) :
    PhysSym (chartData (contentP U n0Param) kParam)).1 = some L ∧ L.2 = true) ↔ _
  have e : (decodeSym (encodeConfig sParam (hyb sParam cS ω t) 0) :
      PhysSym (chartData (contentP U n0Param) kParam)) = hyb sParam cS ω t 0 := by
    simp [decodeSym, encodeConfig]
  rw [e]
  rfl

/-- **The memory clause of Theorem 9.3** (Theorem 7.3 as `Branches` needs it): if `U(n)` does not
halt, `ε ∈ I_n`, the bit-1 and bit-0 initial laws are translation invariant probability laws, and
the one-site cylinder "live data with bit `1`" keeps probability `≥ 1 - S > 3/4` from the first and
`≤ S < 1/4` from the second at every time: memory with `α = 1/2`. -/
theorem memory_branch (hn : 1 ≤ n) (hU : ¬ U.HaltsOn n) {ε : ℝ}
    (hε : ε ∈ UND.window loF hiF n) :
    ∃ μ μ' : Measure (theCA U).Config, IsProbabilityMeasure μ ∧ IsProbabilityMeasure μ' ∧
      (theCA U).IsTranslationInvariant μ ∧ (theCA U).IsTranslationInvariant μ' ∧
      (theCA U).HasMemoryFrom ε μ μ' := by
  have hR := regime_final hn hε
  have h0 := hR.eps_nonneg
  have h1 := hR.eps_le
  have hN := nhalt_cutOf hn hU
  obtain ⟨τ0, hτ0⟩ := ae_typical.exists
  let t0 : RTile (contentP U n0Param) kParam :=
    ⟨rawOf U n0Param kParam (cutOf n) τ0 0, raw_tileOK hτ0 hN 0⟩
  have hp1 := memLaw_prob (n := n) t0 true h0 h1
  have hp0 := memLaw_prob (n := n) t0 false h0 h1
  have hcyl := (ruleCA (chartData (contentP U n0Param) kParam) sParam).measurableSet_cyl win0 (liveOne U)
  -- bit 0: the cylinder forces a data error
  have hlow : ∀ t : ℕ, (ruleCA (chartData (contentP U n0Param) kParam) sParam).law ε (memLaw (n := n) t0 false ε) t ((ruleCA (chartData (contentP U n0Param) kParam) sParam).cyl win0 (liveOne U)) ≤
      ENNReal.ofReal Smem := by
    intro t
    refine law_memLaw_le hn hU hε t0 false t _ hcyl fun τ hτ ω hω => ?_
    obtain ⟨L, hL, hb⟩ := (mem_cyl_liveOne _ ω t).1 hω
    intro h
    rw [hL] at h
    have := congrArg Prod.snd (Option.some_inj.1 h)
    rw [hb] at this
    exact absurd this (by simp [liftChart])
  -- bit 1: the complement forces a data error
  have hhigh : ∀ t : ℕ, (ruleCA (chartData (contentP U n0Param) kParam) sParam).law ε (memLaw (n := n) t0 true ε) t ((ruleCA (chartData (contentP U n0Param) kParam) sParam).cyl win0 (liveOne U))ᶜ ≤
      ENNReal.ofReal Smem := by
    intro t
    refine law_memLaw_le hn hU hε t0 true t _ hcyl.compl fun τ hτ ω hω => ?_
    intro h
    apply hω
    exact (mem_cyl_liveOne _ ω t).2 ⟨_, h, rfl⟩
  refine ⟨memLaw (n := n) t0 true ε, memLaw (n := n) t0 false ε, hp1, hp0,
    memLaw_TI t0 true h0 h1, memLaw_TI t0 false h0 h1,
    ⟨win0, liveOne U, 1 / 2, by norm_num, fun t => ?_⟩⟩
  have hq1 := (ruleCA (chartData (contentP U n0Param) kParam) sParam).isProbabilityMeasure_law h0 h1 (memLaw (n := n) t0 true ε) t
  have hq0 := (ruleCA (chartData (contentP U n0Param) kParam) sParam).isProbabilityMeasure_law h0 h1 (memLaw (n := n) t0 false ε) t
  have hS0 := Smem_nonneg
  have hS1 := Smem_lt
  have ha : ((ruleCA (chartData (contentP U n0Param) kParam) sParam).law ε (memLaw (n := n) t0 false ε) t ((ruleCA (chartData (contentP U n0Param) kParam) sParam).cyl win0 (liveOne U))).toReal ≤ Smem :=
    ENNReal.toReal_le_of_le_ofReal hS0 (hlow t)
  have hb : ((ruleCA (chartData (contentP U n0Param) kParam) sParam).law ε (memLaw (n := n) t0 true ε) t ((ruleCA (chartData (contentP U n0Param) kParam) sParam).cyl win0 (liveOne U))ᶜ).toReal ≤ Smem :=
    ENNReal.toReal_le_of_le_ofReal hS0 (hhigh t)
  have hsum := measure_add_measure_compl (μ := (ruleCA (chartData (contentP U n0Param) kParam) sParam).law ε (memLaw (n := n) t0 true ε) t) hcyl
  rw [measure_univ] at hsum
  have hsum' : ((ruleCA (chartData (contentP U n0Param) kParam) sParam).law ε (memLaw (n := n) t0 true ε) t ((ruleCA (chartData (contentP U n0Param) kParam) sParam).cyl win0 (liveOne U))).toReal +
      ((ruleCA (chartData (contentP U n0Param) kParam) sParam).law ε (memLaw (n := n) t0 true ε) t ((ruleCA (chartData (contentP U n0Param) kParam) sParam).cyl win0 (liveOne U))ᶜ).toReal = 1 := by
    rw [← ENNReal.toReal_add (measure_ne_top _ _) (measure_ne_top _ _), hsum, ENNReal.toReal_one]
  show ((ruleCA (chartData (contentP U n0Param) kParam) sParam).law ε (memLaw (n := n) t0 false ε) t ((ruleCA (chartData (contentP U n0Param) kParam) sParam).cyl win0 (liveOne U))).toReal + 1 / 2 ≤
    ((ruleCA (chartData (contentP U n0Param) kParam) sParam).law ε (memLaw (n := n) t0 true ε) t ((ruleCA (chartData (contentP U n0Param) kParam) sParam).cyl win0 (liveOne U))).toReal
  linarith

/-- **Theorem 7.3**: if `U(n)` does not halt, then for every `ε ∈ I_n` the perturbation has two
distinct spatially translation-invariant stationary laws. -/
theorem theorem_7_3 (hn : 1 ≤ n) (hU : ¬ U.HaltsOn n) {ε : ℝ}
    (hε : ε ∈ UND.window loF hiF n) : (theCA U).HasTwoTIStationaryLaws ε := by
  obtain ⟨μ, μ', hμ, hμ', hti, hti', hmem⟩ := memory_branch hn hU hε
  have hR := regime_final hn hε
  exact (theCA U).hasTwoTIStationaryLaws_of_memory hR.eps_nonneg hR.eps_le hti hti' hmem

/-- **Theorem 9.3 (Theorem A) from the halting branch alone**: with Theorem 7.3 proved, Theorem A
follows from almost sure uniqueness of complete trajectories at time `0` on the halting windows
(Lemma 8.4, the remaining branch of `Branches`). -/
theorem theoremA_of_halting
    (h : ∀ U : Machine, ∀ n : ℕ, 1 ≤ n → ∀ ε ∈ UND.window loF hiF n, U.HaltsOn n →
      ∀ᵐ ω ∂((theCA U).noiseLaw₂ ε), ∀ X Y : ℤ → (theCA U).Config,
        (theCA U).IsComplete ω X → (theCA U).IsComplete ω Y → X 0 = Y 0) : TheoremA :=
  theoremA_of_theCA fun U n hn ε hε => ⟨fun hU => memory_branch hn hU hε, h U n hn ε hε⟩

end UND.Memory
