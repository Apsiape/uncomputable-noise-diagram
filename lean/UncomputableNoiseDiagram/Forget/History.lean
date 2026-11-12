/-
# Section 8.2: packing the historical queries (F2, the probabilistic core)

Part of node F2 of `BLUEPRINT.md` (Part A.8), NEW.

Paper (Lemma 8.2, proof): "At a sampled vertex of this path apply Lemma 8.1. If it supplies
`𝒳^φ`, move one path step backwards. If it supplies a wrong deep query, attach its contour from
Lemma 5.4 and restart at the path vertex one time before its earliest flag. The selected time slabs
are disjoint. … The two event families can share raw atoms. Hölder's inequality and (20) give the
valid joint weight `ε^{3f/4}ρ_B^{m₀/4}`. … The geometric tail excludes the infinite path."

Formalization (generic: a planar site is fixed; nodes are `(t, P)`; `Bad` an intrinsic event per
node, determined by atoms of the node's time, pairwise disjoint across times; the deep roots
`root x ℓ`):
* a *historical path* (`HPath`): an infinite backward path of ordinary centre steps
  `P ↦ P + s_π`, `t ↦ t - 1`, each vertex carrying `Bad` or, at some lag `ℓ ≤ W`, a deep contour
  (`DeepC`: `f ≥ 11` flags, the flag set of an encoding of at most `50(f - 1)` edges of the deep
  graph at the lag-`ℓ` root, flag times in `[t - W - 50(f-1), t - 1]`);
* witnesses of `r` blocks (`Fin r → Blk`): an intrinsic step `inl π`, or a deep block
  `inr (f, ℓ, A, δ)` restarting `gap f = W + 50(f-1) + 1` steps later at provider displacement
  `δ ∈ [0, 175 gap]⁴` (`nxt`); validity (`ok`), the intrinsic events (`badSet`), the flags
  (`flagSet`, disjoint time slabs: `card_flagSet`), the witness event `WEv`;
* **`measure_WEv_le`**: `P(WEv) ≤ α^{m₀} γ^{3f}` (the Hölder step `min(x⁴, y⁴) ≤ x y³` with
  `ρ ≤ α⁴`, `ε ≤ γ⁴`; independence of the intrinsic events at distinct times, `measure_badSet_le`;
  `ε^{|flags|}` for the flags);
* **`tsum_wt_le`**: the weights of `r`-block witnesses sum to at most `β^r` when every node's block
  weights sum to at most `β` (`Fin.consEquiv`, `ENNReal.tsum_prod'`);
* **`exists_witness`** (every historical path has an `r`-block witness, for every `r`), and
  **`hpath_null`**: `P(HPath) = 0` when `β < 1`; **`blk_sum_le`** bounds a node's block weights
  by `qα + Σ_{f ≥ 11} (W+1)·4(2(36q)²)^{50(f-1)}(175 gap(f) + 1)⁴ γ^{3f}`.
-/
import UncomputableNoiseDiagram.Contour.Deep
import UncomputableNoiseDiagram.Memory.Ride

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- `DecidableEq (Sym2 (Pt × ℕ))` has instance size 150 (default limit 128)
set_option synthInstance.maxSize 512

noncomputable section

open MeasureTheory
open scoped ENNReal

namespace UND.Forget

open UND.Rule UND.Sensors UND.Raw UND.Deep UND.Counting
open FNE (Plane)
open UND.Memory (flagAt)

/-- Nodes of a historical path: a time and a provider coordinate (the planar site is fixed). -/
abbrev Node := ℤ × (Fin 4 → ℤ)

/-- Witness blocks: an intrinsic step through a provider (`inl π`), or a deep block
`(f, ℓ, A, δ)` (`f` flags, lag `ℓ`, the flag set `A` as level-`0` vertices of the deep graph, the
provider displacement `δ` of the restart). -/
abbrev Blk := Prov ⊕ (ℕ × ℕ × Finset (Pt × ℕ) × (Fin 4 → ℤ))

section Witness

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData B τ}
variable (W : ℕ) (root : Node → ℕ → Pt × ℕ)

/-- The restart gap of a deep block with `f` flags: `W + 50(f - 1) + 1`. -/
def gap (f : ℕ) : ℕ := W + 50 * (f - 1) + 1

/-- Provider displacements of `n` ordinary steps: `[0, 175 n]⁴`. -/
def boxP (n : ℕ) : Finset (Fin 4 → ℤ) := Fintype.piFinset fun _ => Finset.Icc (0 : ℤ) (175 * n)

/-- The node after a block. -/
def nxt (x : Node) : Blk → Node
  | .inl π => (x.1 - 1, x.2 + provOff π)
  | .inr d => (x.1 - gap W d.1, x.2 + d.2.2.2)

/-- The flag sets of the deep encodings with at most `50(f - 1)` edges at the lag-`ℓ` root. -/
def flagSets (x : Node) (f ℓ : ℕ) : Finset (Finset (Pt × ℕ)) :=
  (encLe nbrD (root x ℓ) (50 * (f - 1))).image Prod.snd

/-- The flag conditions of a deep contour at `x` (lag `ℓ`, `f` flags, flag set `A`). -/
def DFlags (x : Node) (f ℓ : ℕ) (A : Finset (Pt × ℕ)) : Prop :=
  11 ≤ f ∧ ℓ ≤ W ∧ A ∈ flagSets root x f ℓ ∧ A.card = f ∧
    ∀ y ∈ A, y.2 = 0 ∧ y.1.2 ≤ x.1 - 1 ∧ x.1 - y.1.2 ≤ ((W + 50 * (f - 1) : ℕ) : ℤ)

/-- A valid block at `x`. -/
def valid (x : Node) : Blk → Prop
  | .inl _ => True
  | .inr d => DFlags W root x d.1 d.2.1 d.2.2.1 ∧ d.2.2.2 ∈ boxP (gap W d.1)

/-- The intrinsic event of a block. -/
def blkBad (Bad : Node → Set (PNoise CD)) (x : Node) : Blk → Set (PNoise CD)
  | .inl _ => Bad x
  | .inr _ => Set.univ

/-- The atoms of a block's intrinsic event. -/
def blkAtoms (atoms : Node → Finset (ℤ × UND.Site 6)) (x : Node) : Blk → Finset (ℤ × UND.Site 6)
  | .inl _ => atoms x
  | .inr _ => ∅

/-- The flags of a block. -/
def blkFlags : Blk → Finset Pt
  | .inl _ => ∅
  | .inr d => d.2.2.1.image Prod.fst

/-- Intrinsic steps counted by a block. -/
def blkX : Blk → ℕ
  | .inl _ => 1
  | .inr _ => 0

/-- Flags counted by a block. -/
def blkF : Blk → ℕ
  | .inl _ => 0
  | .inr d => d.1

/-- All blocks of a witness are valid. -/
def ok : (r : ℕ) → Node → (Fin r → Blk) → Prop
  | 0, _, _ => True
  | r + 1, x, f => valid W root x (f 0) ∧ ok r (nxt W x (f 0)) (Fin.tail f)

/-- The intrinsic events of a witness. -/
def badSet (Bad : Node → Set (PNoise CD)) : (r : ℕ) → Node → (Fin r → Blk) → Set (PNoise CD)
  | 0, _, _ => Set.univ
  | r + 1, x, f => blkBad Bad x (f 0) ∩ badSet Bad r (nxt W x (f 0)) (Fin.tail f)

/-- The atoms of the intrinsic events of a witness. -/
def atomSet (atoms : Node → Finset (ℤ × UND.Site 6)) :
    (r : ℕ) → Node → (Fin r → Blk) → Finset (ℤ × UND.Site 6)
  | 0, _, _ => ∅
  | r + 1, x, f => blkAtoms atoms x (f 0) ∪ atomSet atoms r (nxt W x (f 0)) (Fin.tail f)

/-- The flags of a witness. -/
def flagSet : (r : ℕ) → Node → (Fin r → Blk) → Finset Pt
  | 0, _, _ => ∅
  | r + 1, x, f => blkFlags (f 0) ∪ flagSet r (nxt W x (f 0)) (Fin.tail f)

/-- The number of intrinsic steps of a witness. -/
def nX : (r : ℕ) → (Fin r → Blk) → ℕ
  | 0, _ => 0
  | r + 1, f => blkX (f 0) + nX r (Fin.tail f)

/-- The number of flags of a witness. -/
def nF : (r : ℕ) → (Fin r → Blk) → ℕ
  | 0, _ => 0
  | r + 1, f => blkF (f 0) + nF r (Fin.tail f)

open Classical in
/-- The weight of a block: `α` for an intrinsic step, `γ^{3f}` for a valid deep block. -/
def blkW (α γ : ℝ≥0∞) (x : Node) (b : Blk) : ℝ≥0∞ :=
  if valid W root x b then α ^ blkX b * γ ^ (3 * blkF b) else 0

/-- The weight of a witness. -/
def wt (α γ : ℝ≥0∞) : (r : ℕ) → Node → (Fin r → Blk) → ℝ≥0∞
  | 0, _, _ => 1
  | r + 1, x, f => blkW W root α γ x (f 0) * wt α γ r (nxt W x (f 0)) (Fin.tail f)

/-- The event of a witness: valid, its intrinsic events, its flags. -/
def WEv (Bad : Node → Set (PNoise CD)) (r : ℕ) (x : Node) (f : Fin r → Blk) :
    Set (PNoise CD) :=
  {_ω | ok W root r x f} ∩ badSet W Bad r x f ∩
    {ω | ∀ p ∈ flagSet W r x f, flagAt ω p.2 p.1 = true}

/-! ### Deterministic facts -/

theorem nxt_time (x : Node) (b : Blk) : (nxt W x b).1 ≤ x.1 - 1 := by
  cases b with
  | inl π => exact le_rfl
  | inr d => simp only [nxt, gap]; push_cast; omega

theorem flagSet_time : ∀ (r : ℕ) (x : Node) (f : Fin r → Blk), ok W root r x f →
    ∀ p ∈ flagSet W r x f, p.2 ≤ x.1 - 1
  | 0, _, _, _, p, hp => by simp [flagSet] at hp
  | r + 1, x, f, h, p, hp => by
    rcases Finset.mem_union.mp hp with hp | hp
    · cases hb : f 0 with
      | inl π => rw [hb] at hp; simp [blkFlags] at hp
      | inr d =>
        have hv := h.1
        rw [hb] at hp hv
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
        exact (hv.1.2.2.2.2 y hy).2.1
    · have := flagSet_time r _ _ h.2 p hp
      have := nxt_time W x (f 0)
      omega

theorem card_flagSet : ∀ (r : ℕ) (x : Node) (f : Fin r → Blk), ok W root r x f →
    (flagSet W r x f).card = nF r f
  | 0, _, _, _ => by simp [flagSet, nF]
  | r + 1, x, f, h => by
    have ih := card_flagSet r _ _ h.2
    have hv := h.1
    simp only [flagSet, nF]
    cases hb : f 0 with
    | inl π =>
      rw [hb] at ih
      simp [blkFlags, blkF, ih]
    | inr d =>
      rw [hb] at hv ih
      have hdisj : Disjoint (blkFlags (Sum.inr d)) (flagSet W r (nxt W x (Sum.inr d)) (Fin.tail f)) := by
        rw [Finset.disjoint_left]
        intro p hp hp'
        obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hp
        have h1 := (hv.1.2.2.2.2 y hy).2.2
        have hok : ok W root r (nxt W x (Sum.inr d)) (Fin.tail f) := by rw [← hb]; exact h.2
        have h2 := flagSet_time W root r _ _ hok y.1 hp'
        simp only [nxt, gap] at h2
        push_cast at h1 h2
        omega
      rw [Finset.card_union_of_disjoint hdisj, ih]
      congr 1
      simp only [blkFlags, blkF]
      rw [Finset.card_image_of_injOn, hv.1.2.2.2.1]
      intro y hy y' hy' hyy
      exact Prod.ext hyy ((hv.1.2.2.2.2 y hy).1.trans (hv.1.2.2.2.2 y' hy').1.symm)

theorem wt_eq (α γ : ℝ≥0∞) : ∀ (r : ℕ) (x : Node) (f : Fin r → Blk), ok W root r x f →
    wt W root α γ r x f = α ^ nX r f * γ ^ (3 * nF r f)
  | 0, _, _, _ => by simp [wt, nX, nF]
  | r + 1, x, f, h => by
    classical
    simp only [wt, nX, nF, blkW, h.1, ↓reduceIte]
    rw [wt_eq α γ r _ _ h.2]
    rw [pow_add, mul_add, pow_add]
    ring

theorem atomSet_time (atoms : Node → Finset (ℤ × UND.Site 6)) :
    ∀ (r : ℕ) (x : Node) (f : Fin r → Blk) (p : ℤ × UND.Site 6),
      p ∈ atomSet W atoms r x f → ∃ z : Node, z.1 ≤ x.1 ∧ p ∈ atoms z
  | 0, _, _, p, hp => by simp [atomSet] at hp
  | r + 1, x, f, p, hp => by
    rcases Finset.mem_union.mp hp with hp | hp
    · cases hb : f 0 with
      | inl π => rw [hb] at hp; exact ⟨x, le_rfl, hp⟩
      | inr d => rw [hb] at hp; simp [blkAtoms] at hp
    · obtain ⟨z, hz, hpz⟩ := atomSet_time atoms r _ _ p hp
      exact ⟨z, hz.trans ((nxt_time W x (f 0)).trans (by omega)), hpz⟩

end Witness

/-! ### Probability of one witness -/

section Prob

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData B τ}
variable (W : ℕ) (root : Node → ℕ → Pt × ℕ)
variable {ν : Measure (Bool × Fin (Fintype.card (PhysSym CD)))} [IsProbabilityMeasure ν]

theorem detBy_badSet (Bad : Node → Set (PNoise CD)) (atoms : Node → Finset (ℤ × UND.Site 6))
    (hdet : ∀ x, DetBy (atoms x) (Bad x)) :
    ∀ (r : ℕ) (x : Node) (f : Fin r → Blk), DetBy (atomSet W atoms r x f) (badSet W Bad r x f)
  | 0, _, _ => fun _ _ _ => Iff.rfl
  | r + 1, x, f => by
    intro ω ω' h
    have h1 : ω ∈ blkBad Bad x (f 0) ↔ ω' ∈ blkBad Bad x (f 0) := by
      cases hb : f 0 with
      | inl π =>
        exact hdet x ω ω' fun i hi => h i (Finset.mem_union_left _ (by rw [hb]; exact hi))
      | inr d => exact Iff.rfl
    have h2 := detBy_badSet Bad atoms hdet r (nxt W x (f 0)) (Fin.tail f) ω ω'
      fun i hi => h i (Finset.mem_union_right _ hi)
    show ω ∈ blkBad Bad x (f 0) ∩ _ ↔ ω' ∈ blkBad Bad x (f 0) ∩ _
    simp only [Set.mem_inter_iff, h1, h2]

/-- **Independence of the intrinsic events** of a witness (at distinct times, on disjoint atoms):
`P(badSet) ≤ ρ^{m₀}`. -/
theorem measure_badSet_le (Bad : Node → Set (PNoise CD))
    (atoms : Node → Finset (ℤ × UND.Site 6)) (hdet : ∀ x, DetBy (atoms x) (Bad x))
    (hdisj : ∀ x z : Node, x.1 ≠ z.1 → Disjoint (atoms x) (atoms z)) (ρ : ℝ≥0∞)
    (hρ : ∀ x, Measure.infinitePi (fun _ : ℤ × UND.Site 6 => ν) (Bad x) ≤ ρ) :
    ∀ (r : ℕ) (x : Node) (f : Fin r → Blk),
      Measure.infinitePi (fun _ : ℤ × UND.Site 6 => ν) (badSet W Bad r x f) ≤ ρ ^ nX r f
  | 0, _, _ => by simp [badSet, nX]
  | r + 1, x, f => by
    have ih := measure_badSet_le Bad atoms hdet hdisj ρ hρ r (nxt W x (f 0)) (Fin.tail f)
    have hm : ∀ r' x' f', MeasurableSet (badSet W Bad r' x' f') := fun r' x' f' =>
      measurableSet_of_detBy (detBy_badSet W Bad atoms hdet r' x' f')
    simp only [badSet, nX]
    cases hb : f 0 with
    | inr d =>
      simp only [blkBad, blkX, Set.univ_inter, zero_add]
      rw [hb] at ih
      exact ih
    | inl π =>
      simp only [blkBad, blkX]
      have hD : Disjoint (atoms x) (atomSet W atoms r (nxt W x (Sum.inl π)) (Fin.tail f)) := by
        rw [Finset.disjoint_left]
        intro p hp hp'
        obtain ⟨z, hz, hpz⟩ := atomSet_time W atoms r _ _ p hp'
        have hzt : z.1 ≤ x.1 - 1 := hz.trans (nxt_time W x _)
        exact Finset.disjoint_left.mp (hdisj x z (by omega)) hp hpz
      rw [infinitePi_inter_eq_mul hD (measurableSet_of_detBy (hdet x)) (hm _ _ _) (hdet x)
        (detBy_badSet W Bad atoms hdet _ _ _), pow_add, pow_one]
      rw [hb] at ih
      exact mul_le_mul' (hρ x) ih

/-- The Hölder step: `min(x⁴, y⁴) ≤ x y³` for `x, y ≤ 1`. -/
theorem le_mul_pow_three {A x y : ℝ≥0∞} (h1 : A ≤ x ^ 4)
    (h2 : A ≤ y ^ 4) : A ≤ x * y ^ 3 := by
  rcases le_total x y with hxy | hxy
  · calc A ≤ x ^ 4 := h1
      _ = x * x ^ 3 := by ring
      _ ≤ x * y ^ 3 := by gcongr
  · calc A ≤ y ^ 4 := h2
      _ = y * y ^ 3 := by ring
      _ ≤ x * y ^ 3 := by gcongr

/-- **One witness**: `P(WEv) ≤ α^{m₀} γ^{3f}` when `ρ ≤ α⁴`, `ε ≤ γ⁴` (Hölder: the intrinsic
events and the flags may share atoms). -/
theorem measure_WEv_le (Bad : Node → Set (PNoise CD))
    (atoms : Node → Finset (ℤ × UND.Site 6)) (hdet : ∀ x, DetBy (atoms x) (Bad x))
    (hdisj : ∀ x z : Node, x.1 ≠ z.1 → Disjoint (atoms x) (atoms z)) (ρ e α γ : ℝ≥0∞)
    (hρ : ∀ x, Measure.infinitePi (fun _ : ℤ × UND.Site 6 => ν) (Bad x) ≤ ρ)
    (hflag : ∀ S : Finset Pt, Measure.infinitePi (fun _ : ℤ × UND.Site 6 => ν)
      {ω : PNoise CD | ∀ p ∈ S, flagAt ω p.2 p.1 = true} ≤ e ^ S.card)
    (hρα : ρ ≤ α ^ 4) (heγ : e ≤ γ ^ 4)
    (r : ℕ) (x : Node) (f : Fin r → Blk) :
    Measure.infinitePi (fun _ : ℤ × UND.Site 6 => ν) (WEv W root Bad r x f) ≤
      wt W root α γ r x f := by
  by_cases h : ok W root r x f
  · rw [wt_eq W root α γ r x f h]
    have hpow : ∀ n : ℕ, (α ^ n) ^ 4 = (α ^ 4) ^ n ∧ (γ ^ n) ^ 4 = (γ ^ 4) ^ n := fun n =>
      ⟨by rw [← pow_mul, ← pow_mul, mul_comm], by rw [← pow_mul, ← pow_mul, mul_comm]⟩
    have e3 : γ ^ (3 * nF r f) = (γ ^ nF r f) ^ 3 := by rw [← pow_mul, mul_comm]
    rw [e3]
    refine le_mul_pow_three ?_ ?_
    · calc _ ≤ Measure.infinitePi (fun _ : ℤ × UND.Site 6 => ν) (badSet W Bad r x f) :=
            measure_mono fun ω hω => hω.1.2
        _ ≤ ρ ^ nX r f := measure_badSet_le W Bad atoms hdet hdisj ρ hρ r x f
        _ ≤ (α ^ 4) ^ nX r f := by gcongr
        _ = (α ^ nX r f) ^ 4 := (hpow _).1.symm
    · calc _ ≤ Measure.infinitePi (fun _ : ℤ × UND.Site 6 => ν)
              {ω : PNoise CD | ∀ p ∈ flagSet W r x f, flagAt ω p.2 p.1 = true} :=
            measure_mono fun ω hω => hω.2
        _ ≤ e ^ (flagSet W r x f).card := hflag _
        _ = e ^ nF r f := by rw [card_flagSet W root r x f h]
        _ ≤ (γ ^ 4) ^ nF r f := by gcongr
        _ = (γ ^ nF r f) ^ 4 := (hpow _).2.symm
  · have : WEv W root Bad r x f = ∅ := by
      ext ω
      simp only [WEv, Set.mem_inter_iff, Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false]
      exact fun h' => h h'.1.1
    rw [this, measure_empty]
    exact zero_le

end Prob

/-! ### Summing the witnesses -/

section Sum

variable (W : ℕ) (root : Node → ℕ → Pt × ℕ)

/-- **The weights of `r`-block witnesses** sum to at most `β^r` when the block weights at every
node sum to at most `β`. -/
theorem tsum_wt_le (α γ β : ℝ≥0∞) (hβ : ∀ x, ∑' b : Blk, blkW W root α γ x b ≤ β) :
    ∀ (r : ℕ) (x : Node), ∑' f : Fin r → Blk, wt W root α γ r x f ≤ β ^ r
  | 0, x => by
    rw [tsum_eq_single (fun i => (Fin.elim0 i : Blk)) fun f hf => (hf (funext fun i => i.elim0)).elim]
    simp [wt]
  | r + 1, x => by
    rw [← (Fin.consEquiv fun _ => Blk).tsum_eq, ENNReal.tsum_prod']
    calc ∑' (b : Blk) (g : Fin r → Blk),
          wt W root α γ (r + 1) x ((Fin.consEquiv fun _ => Blk) (b, g))
        = ∑' b : Blk, blkW W root α γ x b * ∑' g : Fin r → Blk,
            wt W root α γ r (nxt W x b) g := by
          refine tsum_congr fun b => ?_
          rw [← ENNReal.tsum_mul_left]
          refine tsum_congr fun g => ?_
          simp [wt, Fin.consEquiv]
      _ ≤ ∑' b : Blk, blkW W root α γ x b * β ^ r :=
          ENNReal.tsum_le_tsum fun b => by gcongr; exact tsum_wt_le α γ β hβ r _
      _ = (∑' b : Blk, blkW W root α γ x b) * β ^ r := ENNReal.tsum_mul_right
      _ ≤ β * β ^ r := by gcongr; exact hβ x
      _ = β ^ (r + 1) := by rw [pow_succ, mul_comm]

end Sum

/-! ### Historical paths -/

section Path

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData B τ}
variable (W : ℕ) (root : Node → ℕ → Pt × ℕ)

/-- A deep contour at the lag-`ℓ` root of `x`: `f ≥ 11` flags forming the flag set of an encoding
of at most `50(f - 1)` deep edges, in the slab `[t - W - 50(f - 1), t - 1]`, all flagged. -/
def DeepC (ω : PNoise CD) (x : Node) (ℓ : ℕ) : Prop :=
  ∃ f : ℕ, ∃ A : Finset (Pt × ℕ), DFlags W root x f ℓ A ∧ ∀ y ∈ A, flagAt ω y.1.2 y.1.1 = true

/-- **A historical path** from `x`: an infinite backward path of ordinary centre steps, each vertex
carrying its intrinsic event or a deep contour at some lag. -/
def HPath (Bad : Node → Set (PNoise CD)) (ω : PNoise CD) (x : Node) : Prop :=
  ∃ p : ℕ → Fin 4 → ℤ, p 0 = x.2 ∧ (∀ k, ∃ π : Prov, p (k + 1) = p k + provOff π) ∧
    ∀ k : ℕ, ω ∈ Bad (x.1 - k, p k) ∨ ∃ ℓ, DeepC W root ω (x.1 - k, p k) ℓ

theorem path_disp {p : ℕ → Fin 4 → ℤ} (hp : ∀ k, ∃ π : Prov, p (k + 1) = p k + provOff π) :
    ∀ n : ℕ, p n - p 0 ∈ boxP n := by
  intro n
  induction n with
  | zero =>
    simp only [boxP, sub_self, Fintype.mem_piFinset, Finset.mem_Icc]
    intro i
    simp
  | succ n ih =>
    obtain ⟨π, hπ⟩ := hp n
    simp only [boxP, Fintype.mem_piFinset, Finset.mem_Icc] at ih ⊢
    intro i
    rw [hπ]
    have := provOff_mem π i
    have := ih i
    simp only [Pi.sub_apply, Pi.add_apply] at *
    push_cast
    constructor <;> linarith

/-- **Every historical path has a witness of `r` blocks**, for every `r`. -/
theorem exists_witness (Bad : Node → Set (PNoise CD)) (ω : PNoise CD) :
    ∀ (r : ℕ) (x : Node), HPath W root Bad ω x → ∃ f : Fin r → Blk, ω ∈ WEv W root Bad r x f
  | 0, x, _ => ⟨Fin.elim0, ⟨⟨trivial, trivial⟩, fun p hp => by simp [flagSet] at hp⟩⟩
  | r + 1, x, ⟨p, hp0, hstep, hnode⟩ => by
    have hx : (x.1 - ((0 : ℕ) : ℤ), p 0) = x := by rw [hp0]; simp
    rcases hnode 0 with hbad | ⟨ℓ, f, A, hD, hfl⟩
    all_goals rw [hx] at *
    · obtain ⟨π, hπ⟩ := hstep 0
      have hnext : HPath W root Bad ω (nxt W x (Sum.inl π)) := by
        refine ⟨fun k => p (k + 1), ?_, fun k => hstep (k + 1), fun k => ?_⟩
        · simp only [nxt, zero_add, hπ, hp0]
        · have := hnode (k + 1)
          simp only [nxt]
          rwa [show x.1 - ((k + 1 : ℕ) : ℤ) = x.1 - 1 - (k : ℤ) by push_cast; ring] at this
      obtain ⟨g, hg⟩ := exists_witness Bad ω r _ hnext
      refine ⟨Fin.cons (Sum.inl π) g, ?_⟩
      have h0 : (Fin.cons (Sum.inl π) g : Fin (r + 1) → Blk) 0 = Sum.inl π := rfl
      have ht : Fin.tail (Fin.cons (Sum.inl π) g : Fin (r + 1) → Blk) = g := Fin.tail_cons _ _
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · rw [h0]; trivial
      · rw [h0, ht]; exact hg.1.1
      · show ω ∈ blkBad Bad x _ ∩ badSet W Bad r _ _
        rw [h0, ht]
        exact ⟨hbad, hg.1.2⟩
      · intro q hq
        simp only [flagSet, h0, ht, blkFlags, Finset.empty_union] at hq
        exact hg.2 q hq
    · set n := gap W f with hn
      have hnext : HPath W root Bad ω (x.1 - n, p n) := by
        refine ⟨fun k => p (k + n), by simp, fun k => ?_, fun k => ?_⟩
        · show ∃ π, p (k + 1 + n) = p (k + n) + provOff π
          rw [show k + 1 + n = (k + n) + 1 by ring]; exact hstep (k + n)
        · have := hnode (k + n)
          rwa [show x.1 - ((k + n : ℕ) : ℤ) = x.1 - n - (k : ℤ) by push_cast; ring] at this
      obtain ⟨g, hg⟩ := exists_witness Bad ω r _ hnext
      have hδ := path_disp hstep n
      let b : Blk := Sum.inr (f, ℓ, A, p n - p 0)
      have hnx : nxt W x b = (x.1 - n, p n) := by
        simp only [b, nxt, hn, hp0]
        congr 1
        abel
      refine ⟨Fin.cons b g, ?_⟩
      have h0 : (Fin.cons b g : Fin (r + 1) → Blk) 0 = b := rfl
      have ht : Fin.tail (Fin.cons b g : Fin (r + 1) → Blk) = g := Fin.tail_cons _ _
      refine ⟨⟨⟨?_, ?_⟩, ?_⟩, ?_⟩
      · rw [h0]
        exact ⟨hD, hδ⟩
      · rw [h0, ht, hnx]; exact hg.1.1
      · show ω ∈ blkBad Bad x _ ∩ badSet W Bad r _ _
        rw [h0, ht, hnx]
        exact ⟨trivial, hg.1.2⟩
      · intro q hq
        simp only [flagSet, h0, ht, hnx] at hq
        rcases Finset.mem_union.mp hq with hq | hq
        · obtain ⟨y, hy, rfl⟩ := Finset.mem_image.mp hq
          exact hfl y hy
        · exact hg.2 q hq

end Path

/-! ### The block weights at one node, and the null event -/

section Final

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData B τ}
variable (W : ℕ) (root : Node → ℕ → Pt × ℕ)

theorem card_boxP (n : ℕ) : (boxP n).card = (175 * n + 1) ^ 4 := by
  simp only [boxP, Fintype.card_piFinset, Int.card_Icc, sub_zero, Finset.prod_const,
    Finset.card_univ, Fintype.card_fin]
  congr 1

theorem card_flagSets_le (x : Node) (f ℓ : ℕ) :
    (flagSets root x f ℓ).card ≤ 4 * (2 * (36 * UND.Param.q) ^ 2) ^ (50 * (f - 1)) :=
  Finset.card_image_le.trans (card_encLe_le nbrD _ card_nbrD_le
    (by norm_num [UND.Param.q, UND.Param.K]) _ _)

theorem blkW_le (α γ : ℝ≥0∞) (x : Node) (f : ℕ) (r : ℕ × Finset (Pt × ℕ) × (Fin 4 → ℤ)) :
    blkW W root α γ x (Sum.inr (f, r)) ≤ γ ^ (3 * f) := by
  classical
  unfold blkW
  split_ifs
  · simp [blkX, blkF]
  · exact zero_le

/-- **The block weights at one node**: at most `qα` for the intrinsic steps, plus, for each
`f ≥ 11`, `(W + 1)` lags times `4(2(36q)²)^{50(f-1)}` flag sets times `(175 gap(f) + 1)⁴`
restarts, each of weight `γ^{3f}`. -/
theorem blk_sum_le (α γ : ℝ≥0∞) (x : Node) :
    ∑' b : Blk, blkW W root α γ x b ≤ (UND.Param.q : ℝ≥0∞) * α +
      ∑' f : ℕ, (if 11 ≤ f then (((W + 1) * (4 * (2 * (36 * UND.Param.q) ^ 2) ^ (50 * (f - 1))) *
        (175 * gap W f + 1) ^ 4 : ℕ) : ℝ≥0∞) * γ ^ (3 * f) else 0) := by
  classical
  rw [Summable.tsum_sum ENNReal.summable ENNReal.summable]
  gcongr
  · rw [tsum_fintype]
    have : ∀ π : Prov, blkW W root α γ x (Sum.inl π) = α := fun π => by
      simp [blkW, valid, blkX, blkF]
    simp only [this, Finset.sum_const, Finset.card_univ, card_Prov, nsmul_eq_mul]
    exact le_rfl
  · rw [ENNReal.tsum_prod']
    refine ENNReal.tsum_le_tsum fun f => ?_
    split_ifs with hf
    · set S : Finset (ℕ × Finset (Pt × ℕ) × (Fin 4 → ℤ)) :=
        (Finset.range (W + 1)).biUnion
          (fun ℓ => (flagSets root x f ℓ ×ˢ boxP (gap W f)).image (fun p => (ℓ, p.1, p.2)))
        with hS
      rw [tsum_eq_sum (s := S) ?_]
      · calc ∑ r ∈ S, blkW W root α γ x (Sum.inr (f, r))
            ≤ ∑ _r ∈ S, γ ^ (3 * f) := Finset.sum_le_sum fun r _ => blkW_le W root α γ x f r
          _ = (S.card : ℝ≥0∞) * γ ^ (3 * f) := by rw [Finset.sum_const, nsmul_eq_mul]
          _ ≤ _ := by
            gcongr
            have hc : S.card ≤ (W + 1) * (4 * (2 * (36 * UND.Param.q) ^ 2) ^ (50 * (f - 1)) *
                (175 * gap W f + 1) ^ 4) := by
              refine Finset.card_biUnion_le.trans ?_
              have hterm : ∀ ℓ ∈ Finset.range (W + 1),
                  ((flagSets root x f ℓ ×ˢ boxP (gap W f)).image
                    (fun p => (ℓ, p.1, p.2))).card ≤
                  4 * (2 * (36 * UND.Param.q) ^ 2) ^ (50 * (f - 1)) *
                    (175 * gap W f + 1) ^ 4 := fun ℓ _ =>
                Finset.card_image_le.trans (by
                  rw [Finset.card_product, card_boxP]
                  exact Nat.mul_le_mul_right _ (card_flagSets_le root x f ℓ))
              refine (Finset.sum_le_sum hterm).trans ?_
              rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
            have := mul_assoc (W + 1) (4 * (2 * (36 * UND.Param.q) ^ 2) ^ (50 * (f - 1)))
              ((175 * gap W f + 1) ^ 4)
            rw [this]
            exact_mod_cast hc
      · intro r hr
        unfold blkW
        rw [ite_eq_right_iff]
        intro hv
        exfalso
        refine hr (Finset.mem_biUnion.mpr ⟨r.1, Finset.mem_range.mpr
          (Nat.lt_succ_of_le hv.1.2.1), Finset.mem_image.mpr ⟨(r.2.1, r.2.2), ?_, rfl⟩⟩)
        exact Finset.mem_product.mpr ⟨hv.1.2.2.1, hv.2⟩
    · have : ∀ r, blkW W root α γ x (Sum.inr (f, r)) = 0 := fun r => by
        unfold blkW
        rw [ite_eq_right_iff]
        intro hv
        exact absurd hv.1.1 hf
      simp [this]

variable {ν : Measure (Bool × Fin (Fintype.card (PhysSym CD)))} [IsProbabilityMeasure ν]

/-- **Lemma 8.2, the probabilistic core**: if the block weights at every node sum to at most
`β < 1`, almost surely no historical path starts at `x`. -/
theorem hpath_null (Bad : Node → Set (PNoise CD))
    (atoms : Node → Finset (ℤ × UND.Site 6)) (hdet : ∀ x, DetBy (atoms x) (Bad x))
    (hdisj : ∀ x z : Node, x.1 ≠ z.1 → Disjoint (atoms x) (atoms z)) (ρ e α γ : ℝ≥0∞)
    (hρ : ∀ x, Measure.infinitePi (fun _ : ℤ × UND.Site 6 => ν) (Bad x) ≤ ρ)
    (hflag : ∀ S : Finset Pt, Measure.infinitePi (fun _ : ℤ × UND.Site 6 => ν)
      {ω : PNoise CD | ∀ p ∈ S, flagAt ω p.2 p.1 = true} ≤ e ^ S.card)
    (hρα : ρ ≤ α ^ 4) (heγ : e ≤ γ ^ 4) (β : ℝ≥0∞)
    (hβ : ∀ x, ∑' b : Blk, blkW W root α γ x b ≤ β) (hβ1 : β < 1) (x : Node) :
    Measure.infinitePi (fun _ : ℤ × UND.Site 6 => ν) {ω | HPath W root Bad ω x} = 0 := by
  have hb : ∀ r : ℕ, Measure.infinitePi (fun _ : ℤ × UND.Site 6 => ν)
      {ω | HPath W root Bad ω x} ≤ β ^ r := by
    intro r
    calc Measure.infinitePi (fun _ : ℤ × UND.Site 6 => ν) {ω | HPath W root Bad ω x}
        ≤ Measure.infinitePi (fun _ : ℤ × UND.Site 6 => ν)
            (⋃ f : Fin r → Blk, WEv W root Bad r x f) :=
          measure_mono fun ω hω => Set.mem_iUnion.mpr (exists_witness W root Bad ω r x hω)
      _ ≤ ∑' f : Fin r → Blk, Measure.infinitePi (fun _ : ℤ × UND.Site 6 => ν)
            (WEv W root Bad r x f) := measure_iUnion_le _
      _ ≤ ∑' f : Fin r → Blk, wt W root α γ r x f := ENNReal.tsum_le_tsum fun f =>
          measure_WEv_le W root Bad atoms hdet hdisj ρ e α γ hρ hflag hρα heγ r x f
      _ ≤ β ^ r := tsum_wt_le W root α γ β hβ r x
  exact le_zero_iff.mp (ge_of_tendsto' (ENNReal.tendsto_pow_atTop_nhds_zero_of_lt_one hβ1) hb)

end Final

end UND.Forget
