/-
# Section 6: Lemma 6.1 (ownership of noise atoms) (N2)

Node N2 of `BLUEPRINT.md` (Part A.6), NEW (Mathlib: `iIndepFun_iff_measure_inter_preimage_eq_mul`).

Paper (Lemma 6.1): "For one fixed chart phase, the intrinsic source supports of distinct finite
phase-zero gates are disjoint, over all space and time. Their `B` lanes are independent. The same
assertion holds if a long support is restricted to its recent `W` atoms."
Proof: "A phase-zero row `y` owns the physical rows `y, …, y + B - 1`, using field `j` at row
`y + j`. These blocks partition the rows. Thus a physical update atom is relevant to one field and
one base row. Within a lane the invariant coordinates of a backward copy are
`χ_ch = (x - t, y, P + vt)` (16). For fixed `χ_ch` the end position determines the time and
provider location. Its finite source segment is `[L_d, R_d - 1]` in the `x` coordinate. Successive
true ruler intervals on that row are disjoint. Hence each atom belongs to at most one gate's
source. Restricting supports preserves disjointness."

Formalization:
* independence on pairwise disjoint finite coordinate sets: `detBy_biInter`, `detBy_biUnion`,
  **`infinitePi_biInter_eq_prod`** (events), **`iIndepFun_of_detBy`** (functions),
  `measurableSet_of_detBy` (on a finite alphabet every event determined by finitely many
  coordinates is measurable);
* characteristic coordinates (16): `chSite c y Q t = ((c + t, y), Q - t v)` is the point at time
  `t` of the characteristic `(c, y, Q)`; `laneAtom c y Q j t` is the noise atom (two-sided index)
  of the output at time `t` on the lane characteristic `(c, y + j, Q)`; `laneAtom_inj`;
* the true ride of lane `j` of the gate ending at time `t`: `ride c y Q j t n`, the outputs at times
  `t - 1, …, t - n` (most recent first; `n = ℓ_d` for the provisional end, `n = W` for the recent
  window); `ride_nodup`, `mem_ride`, `ride_disjoint` (distinct lanes use distinct rows);
* `IsGate tc tr k d c y t`: a finite phase-zero gate of depth `d`: the row `y` is `Bot_d` of a
  depth-`d` row frame with `d ≥ k` and the end `c + t` is `R_d` of a depth-`d` column frame;
  `isGate_of_end` (an `End` of lane phase zero on a finite bottom row);
* `phaseZero_block` (phase-zero rows own disjoint blocks of `B = 4^k` rows), `depth_unique`,
  `rightEnd_eq` (depth-`d` ends are `4^{d+1}` apart);
* **`ownership`** (Lemma 6.1): an atom lies on the ride of at most one (gate, lane, step) with step
  `< ℓ_d`; **`gateAtoms_disjoint`** (distinct gates, also with supports restricted to the recent
  `W ≤ ℓ_d` atoms, have disjoint atom sets); `lanes_iIndep` (the `B` lane indicators of one gate
  are independent).
-/
import UncomputableNoiseDiagram.Sensors.Ideal
import UncomputableNoiseDiagram.Chart.Origins

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace UND.Sensors

/-! ## Independence on pairwise disjoint coordinate sets -/

section Indep

variable {I α : Type*} [MeasurableSpace α] [Nonempty α]

theorem detBy_mono {S T : Finset I} (h : S ⊆ T) {A : Set (I → α)} (hA : DetBy S A) :
    DetBy T A :=
  fun ω ω' hω => hA ω ω' (fun i hi => hω i (h hi))

theorem detBy_empty (S : Finset I) : DetBy S (∅ : Set (I → α)) := fun _ _ _ => Iff.rfl

theorem detBy_biInter {ι : Type*} [DecidableEq I] (S : Finset ι) (a : ι → Finset I)
    (A : ι → Set (I → α)) (h : ∀ k ∈ S, DetBy (a k) (A k)) :
    DetBy (S.biUnion a) (⋂ k ∈ S, A k) := by
  intro ω ω' hω
  simp only [Set.mem_iInter]
  exact forall₂_congr fun k hk => h k hk ω ω' (fun i hi => hω i (Finset.mem_biUnion.2 ⟨k, hk, hi⟩))

theorem detBy_biUnion {ι : Type*} [DecidableEq I] (S : Finset ι) (a : ι → Finset I)
    (A : ι → Set (I → α)) (h : ∀ k ∈ S, DetBy (a k) (A k)) :
    DetBy (S.biUnion a) (⋃ k ∈ S, A k) := by
  intro ω ω' hω
  simp only [Set.mem_iUnion]
  exact exists₂_congr fun k hk => h k hk ω ω' (fun i hi => hω i (Finset.mem_biUnion.2 ⟨k, hk, hi⟩))

/-- On a finite alphabet, an event determined by finitely many coordinates is measurable. -/
theorem measurableSet_of_detBy [Finite α] [MeasurableSingletonClass α] {S : Finset I}
    {A : Set (I → α)} (h : DetBy S A) : MeasurableSet A := by
  rw [preimage_of_detBy h]
  have hm : Measurable (fun (ω : I → α) (i : S) => ω i) :=
    measurable_pi_iff.mpr fun i => measurable_pi_apply (i : I)
  exact hm (Set.toFinite _).measurableSet

/-- **Independence of events on pairwise disjoint coordinate sets**: under a product measure, the
intersection of finitely many events determined by pairwise disjoint finite coordinate sets has
the product probability. -/
theorem infinitePi_biInter_eq_prod {P : I → Measure α} [∀ i, IsProbabilityMeasure (P i)]
    {ι : Type*} [DecidableEq ι] [DecidableEq I] (a : ι → Finset I) (A : ι → Set (I → α)) :
    ∀ S : Finset ι, (∀ k ∈ S, ∀ l ∈ S, k ≠ l → Disjoint (a k) (a l)) →
      (∀ k ∈ S, MeasurableSet (A k)) → (∀ k ∈ S, DetBy (a k) (A k)) →
      Measure.infinitePi P (⋂ k ∈ S, A k) = ∏ k ∈ S, Measure.infinitePi P (A k) := by
  intro S
  induction S using Finset.induction_on with
  | empty => intro _ _ _; simp
  | insert k S hk ih =>
    intro hd hA hdet
    have hk0 : k ∈ insert k S := Finset.mem_insert_self _ _
    have hS : ∀ l ∈ S, l ∈ insert k S := fun l hl => Finset.mem_insert_of_mem hl
    rw [Finset.set_biInter_insert, Finset.prod_insert hk]
    have hdisj : Disjoint (a k) (S.biUnion a) := by
      rw [Finset.disjoint_biUnion_right]
      intro l hl
      exact hd k hk0 l (hS l hl) (fun e => hk (e ▸ hl))
    rw [infinitePi_inter_eq_mul hdisj (hA k hk0)
      (Finset.measurableSet_biInter _ fun l hl => hA l (hS l hl)) (hdet k hk0)
      (detBy_biInter S a A fun l hl => hdet l (hS l hl)),
      ih (fun k' hk' l hl => hd k' (hS k' hk') l (hS l hl)) (fun l hl => hA l (hS l hl))
        (fun l hl => hdet l (hS l hl))]

/-- **Functions determined by pairwise disjoint finite coordinate sets are independent** under a
product measure. -/
theorem iIndepFun_of_detBy {P : I → Measure α} [∀ i, IsProbabilityMeasure (P i)]
    {ι β : Type*} [MeasurableSpace β] (a : ι → Finset I)
    (hd : ∀ k l, k ≠ l → Disjoint (a k) (a l)) (f : ι → (I → α) → β)
    (hf : ∀ k, Measurable (f k)) (hdet : ∀ k ω ω', (∀ i ∈ a k, ω i = ω' i) → f k ω = f k ω') :
    iIndepFun f (Measure.infinitePi P) := by
  classical
  rw [iIndepFun_iff_measure_inter_preimage_eq_mul]
  intro S sets hsets
  exact infinitePi_biInter_eq_prod a (fun k => f k ⁻¹' sets k) S (fun k _ l _ hkl => hd k l hkl)
    (fun k hk => hf k (hsets k hk))
    (fun k _ ω ω' h => by simp only [Set.mem_preimage, hdet k ω ω' h])

end Indep

/-! ## Characteristic coordinates and rides -/

section Rides

open UND.Rule

/-- `v = (32, 32, 32, 32)` as a provider vector. -/
def vP : Fin 4 → ℤ := fun _ => 32

/-- (16): the point at time `t` of the characteristic `(c, y, Q)` (invariants `x - t = c`, row `y`,
`P + vt = Q`): planar `(c + t, y)`, provider `Q - t v`. -/
def chSite (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ) : ISite := ((c + t, y), Q - t • vP)

/-- The noise atom (two-sided index) of the output at time `t` on the lane characteristic
`(c, y + j, Q)`. -/
def laneAtom (c y : ℤ) (Q : Fin 4 → ℤ) (j : ℕ) (t : ℤ) : ℤ × UND.Site 6 :=
  (t, siteEquiv.symm (chSite c (y + j) Q t))

theorem laneAtom_inj {c y c' y' : ℤ} {Q Q' : Fin 4 → ℤ} {j j' : ℕ} {t t' : ℤ}
    (h : laneAtom c y Q j t = laneAtom c' y' Q' j' t') :
    t = t' ∧ c = c' ∧ y + j = y' + j' ∧ Q = Q' := by
  simp only [laneAtom, Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  have h3 := siteEquiv.symm.injective h2
  simp only [chSite, Prod.mk.injEq] at h3
  obtain ⟨⟨h4, h5⟩, h6⟩ := h3
  exact ⟨rfl, by linarith, h5, sub_left_inj.mp h6⟩

/-- **The true ride** of lane `j` of the gate ending at proposal time `t` on the base
characteristic `(c, y, Q)`: its `n` most recent update atoms, most recent first (the outputs at
times `t - 1, …, t - n` on the lane characteristic `(c, y + j, Q)`). -/
def ride (c y : ℤ) (Q : Fin 4 → ℤ) (j : ℕ) (t : ℤ) (n : ℕ) : List (ℤ × UND.Site 6) :=
  (List.range n).map fun i : ℕ => laneAtom c y Q j (t - 1 - (i : ℤ))

theorem ride_length (c y : ℤ) (Q : Fin 4 → ℤ) (j : ℕ) (t : ℤ) (n : ℕ) :
    (ride c y Q j t n).length = n := by
  simp [ride]

theorem ride_nodup (c y : ℤ) (Q : Fin 4 → ℤ) (j : ℕ) (t : ℤ) (n : ℕ) :
    (ride c y Q j t n).Nodup := by
  refine List.Nodup.map (fun i i' h => ?_) List.nodup_range
  have := (laneAtom_inj h).1
  exact_mod_cast (by linarith : (i : ℤ) = i')

theorem mem_ride {c y : ℤ} {Q : Fin 4 → ℤ} {j : ℕ} {t : ℤ} {n : ℕ} {p : ℤ × UND.Site 6} :
    p ∈ ride c y Q j t n ↔ ∃ i < n, laneAtom c y Q j (t - 1 - i) = p := by
  simp [ride]

/-- Distinct lanes of one gate ride on distinct physical rows. -/
theorem ride_disjoint (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ) (n : ℕ) {j j' : ℕ} (hj : j ≠ j') :
    Disjoint (ride c y Q j t n).toFinset (ride c y Q j' t n).toFinset := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  rw [List.mem_toFinset, mem_ride] at hp hp'
  obtain ⟨i, -, rfl⟩ := hp
  obtain ⟨i', -, h⟩ := hp'
  have := (laneAtom_inj h).2.2.1
  have e : (j : ℤ) = j' := by linarith
  exact hj (by exact_mod_cast e)

end Rides

/-! ## Gates and their rows -/

section Gates

open UPD.Scaffold UND.Chart

/-- **A finite phase-zero gate** of depth `d` ending at proposal time `t` on the base
characteristic `(c, y, ·)`: the row `y` is the lower endpoint `Bot_d` of a depth-`d` row frame,
`d ≥ k` (lane phase zero, FD2), and the end `c + t` is the right endpoint `R_d` of a depth-`d`
column frame (`tc`, `tr`: the binary digits of the two phase coordinates). -/
def IsGate (tc tr : ℕ → Bool) (k d : ℕ) (c y t : ℤ) : Prop :=
  k ≤ d ∧ IsLeftEnd (phaseOffsets tr) d y ∧ IsRightEnd (phaseOffsets tc) d (c + t)

/-- The row of a finite phase-zero gate has lane phase zero. -/
theorem IsGate.lanePhase {tc tr : ℕ → Bool} {k d : ℕ} {c y t : ℤ} (h : IsGate tc tr k d c y t) :
    lanePhase tr k y = 0 := by
  obtain ⟨hk, ⟨m, rfl⟩, -⟩ := h
  exact (lanePhase_bot_eq_zero_iff tr k d m).2 hk

/-- An `End` of lane phase zero on a finite bottom row is a finite phase-zero gate (§3.2, FD2). -/
theorem isGate_of_end {Y : FNE.Plane → Quarter} {τ : ℕ → Bool × Bool} (hY : IsQPhase Y τ)
    (ξ : FNE.Plane) {r : ℕ} (hr : PRank (row τ) ξ.2 r) (hE : IsEnd (Y ξ)) (k : ℕ)
    (hp : lanePhase (row τ) k ξ.2 = 0) (t : ℤ) :
    ∃ d, 1 ≤ d ∧ IsGate (col τ) (row τ) k d (ξ.1 - t) ξ.2 t := by
  obtain ⟨d, hd, hcol, hrow, hiff⟩ := end_gate hY ξ hr hE k
  refine ⟨d, hd, hiff.1 hp, hrow, ?_⟩
  rwa [sub_add_cancel]

/-- **Phase-zero rows own disjoint blocks**: rows of lane phase zero are `B = 4^k` apart, so
`y + j = y' + j'` with `j, j' < B` forces `y = y'`, `j = j'`. -/
theorem phaseZero_block {tr : ℕ → Bool} {k : ℕ} {y y' : ℤ} {j j' : ℕ}
    (hy : lanePhase tr k y = 0) (hy' : lanePhase tr k y' = 0) (hj : j < 4 ^ k)
    (hj' : j' < 4 ^ k) (h : y + j = y' + j') : y = y' ∧ j = j' := by
  unfold lanePhase at hy hy'
  have h1 := Int.dvd_of_emod_eq_zero hy
  have h2 := Int.dvd_of_emod_eq_zero hy'
  have hd : (4 : ℤ) ^ k ∣ y - y' := by
    have := dvd_sub h1 h2
    rwa [show y - wsum tr (2 * k) - 1 - (y' - wsum tr (2 * k) - 1) = y - y' by ring] at this
  have hj1 : (j : ℤ) < 4 ^ k := by exact_mod_cast hj
  have hj2 : (j' : ℤ) < 4 ^ k := by exact_mod_cast hj'
  have habs : |y - y'| < 4 ^ k := by
    rw [abs_lt]
    constructor <;> linarith [(Nat.cast_nonneg j : (0 : ℤ) ≤ j), (Nat.cast_nonneg j' : (0 : ℤ) ≤ j')]
  have h0 := Int.eq_zero_of_abs_lt_dvd hd habs
  refine ⟨by linarith, ?_⟩
  exact_mod_cast (by linarith : (j : ℤ) = j')

/-- The depth of a finite bottom row is unique. -/
theorem depth_unique (t : ℕ → Bool) {d d' : ℕ} {y : ℤ} (h : IsLeftEnd (phaseOffsets t) d y)
    (h' : IsLeftEnd (phaseOffsets t) d' y) : d = d' :=
  le_antisymm (le_of_end_inFrame t (Or.inl h) (inFrame_of_isLeftEnd h'))
    (le_of_end_inFrame t (Or.inl h') (inFrame_of_isLeftEnd h))

/-- Depth-`d` right endpoints are `4^{d+1}` apart. -/
theorem rightEnd_dvd {a : ℕ → ℤ} {d : ℕ} {x x' : ℤ} (h : IsRightEnd a d x)
    (h' : IsRightEnd a d x') : (4 : ℤ) ^ (d + 1) ∣ x - x' := by
  obtain ⟨m, rfl⟩ := h
  obtain ⟨m', rfl⟩ := h'
  exact ⟨m - m', by simp only [frameHi]; ring⟩

theorem rightEnd_eq {a : ℕ → ℤ} {d : ℕ} {x x' : ℤ} (h : IsRightEnd a d x)
    (h' : IsRightEnd a d x') (hlt : |x - x'| < 4 ^ (d + 1)) : x = x' := by
  have := Int.eq_zero_of_abs_lt_dvd (rightEnd_dvd h h') hlt
  linarith

theorem ell_lt_four_pow (d : ℕ) : ((UND.Windows.ell d : ℕ) : ℤ) < 4 ^ (d + 1) := by
  unfold UND.Windows.ell
  have h1 : 1 ≤ 2 * 4 ^ d := by have := Nat.one_le_pow d 4 (by norm_num); omega
  have h2 : 2 * 4 ^ d - 1 < 4 ^ (d + 1) := by rw [pow_succ]; omega
  exact_mod_cast h2

/-- **Lemma 6.1 (ownership of noise atoms).** For one fixed chart phase, an update atom lies on the
true ride of at most one (finite phase-zero gate, lane, step): if step `i` of lane `j` of the gate
of depth `d` ending at time `t` on `(c, y, Q)` is the atom of step `i'` of lane `j'` of the gate of
depth `d'` ending at time `t'` on `(c', y', Q')`, with `j, j' < B = 4^k`, `i < ℓ_d`, `i' < ℓ_{d'}`,
then the gates, lanes and steps agree. -/
theorem ownership {tc tr : ℕ → Bool} {k d d' : ℕ} {c y c' y' t t' : ℤ} {Q Q' : Fin 4 → ℤ}
    {j j' i i' : ℕ} (hg : IsGate tc tr k d c y t) (hg' : IsGate tc tr k d' c' y' t')
    (hj : j < 4 ^ k) (hj' : j' < 4 ^ k) (hi : i < UND.Windows.ell d)
    (hi' : i' < UND.Windows.ell d')
    (h : laneAtom c y Q j (t - 1 - i) = laneAtom c' y' Q' j' (t' - 1 - i')) :
    d = d' ∧ c = c' ∧ y = y' ∧ Q = Q' ∧ t = t' ∧ j = j' ∧ i = i' := by
  obtain ⟨ht, rfl, hy, rfl⟩ := laneAtom_inj h
  obtain ⟨rfl, rfl⟩ := phaseZero_block hg.lanePhase hg'.lanePhase hj hj' hy
  obtain rfl := depth_unique tr hg.2.1 hg'.2.1
  have hi1 : (i : ℤ) < UND.Windows.ell d := by exact_mod_cast hi
  have hi2 : (i' : ℤ) < UND.Windows.ell d := by exact_mod_cast hi'
  have hl := ell_lt_four_pow d
  have hlt : |(c + t) - (c + t')| < 4 ^ (d + 1) := by
    rw [abs_lt]
    constructor <;> linarith [(Nat.cast_nonneg i : (0 : ℤ) ≤ i),
      (Nat.cast_nonneg i' : (0 : ℤ) ≤ i')]
  have htt : t = t' := by linarith [rightEnd_eq hg.2.2 hg'.2.2 hlt]
  subst htt
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, ?_⟩
  exact_mod_cast (by linarith : (i : ℤ) = i')

/-- The atoms of the `B` lanes of a gate, `n` steps each (`n = ℓ_d` for the provisional end,
`n = W` for the recent window). -/
def gateAtoms (c y : ℤ) (Q : Fin 4 → ℤ) (t : ℤ) (B n : ℕ) : Finset (ℤ × UND.Site 6) :=
  (Finset.range B).biUnion fun j => (ride c y Q j t n).toFinset

theorem mem_gateAtoms {c y : ℤ} {Q : Fin 4 → ℤ} {t : ℤ} {B n : ℕ} {p : ℤ × UND.Site 6} :
    p ∈ gateAtoms c y Q t B n ↔ ∃ j < B, ∃ i < n, laneAtom c y Q j (t - 1 - i) = p := by
  simp [gateAtoms, mem_ride]

/-- **Lemma 6.1, disjoint supports**: distinct finite phase-zero gates have disjoint atom sets,
also when supports are restricted to their most recent `n ≤ ℓ_d` atoms. -/
theorem gateAtoms_disjoint {tc tr : ℕ → Bool} {k d d' : ℕ} {c y c' y' t t' : ℤ}
    {Q Q' : Fin 4 → ℤ} {B n n' : ℕ} (hg : IsGate tc tr k d c y t)
    (hg' : IsGate tc tr k d' c' y' t') (hB : B ≤ 4 ^ k) (hn : n ≤ UND.Windows.ell d)
    (hn' : n' ≤ UND.Windows.ell d') (hne : (c, y, Q, t) ≠ (c', y', Q', t')) :
    Disjoint (gateAtoms c y Q t B n) (gateAtoms c' y' Q' t' B n') := by
  rw [Finset.disjoint_left]
  intro p hp hp'
  rw [mem_gateAtoms] at hp hp'
  obtain ⟨j, hj, i, hi, rfl⟩ := hp
  obtain ⟨j', hj', i', hi', h⟩ := hp'
  obtain ⟨-, rfl, rfl, rfl, rfl, -, -⟩ := ownership hg hg' (by omega) (by omega) (by omega)
    (by omega) h.symm
  exact hne rfl

end Gates

end UND.Sensors
