/-
# Section 5.2: the raw marked set and Lemma 5.3 (coherence of unmarked live letters) (C3)

Node C3 of `BLUEPRINT.md` (Part A.5), NEW (the pigeonhole of the forgetting core's
`card_filter_not_add` is the template for the discards).

Paper (Section 5.2): "Let `𝓜^{t₀}` start empty at physical time `t₀`. Mark each replacement flag
and each site having a marked Moore parent in two distinct provider clusters. Let `𝓜` be its
increasing limit as `t₀ → -∞`."

**Lemma 5.3.** "In every complete trajectory of (6), all unmarked live data or second-coordinate
readings at a fixed planar site and time have the same letter over all provider positions.
Readings at neighbouring planar sites are compatible in all eight Moore directions. If any
unmarked live reading exists, one full legal, time-constant planar chart agrees with every such
reading at every time."

Formalization (deterministic, for any trajectory indexed by `ℤ` with replacement flags `E`, D33):
* the pairing (13): `PSrc` (`5·15·16³` pairs), `pHi`, `pLo` (providers differing by `e_j` in one
  cluster), `provOff_pair`, **`exists_pair`** (`|Bad₁| + |Bad₂| < 5·15·16³` leaves a pair; the
  printed count `[5 - 4 - 5/16]K = 45056 > 0`); the provider separation `sep` (`‖P' - P‖₁`),
  `sep_step`;
* `MarkedAt`, `TwoCl` (marked Moore parents in two distinct clusters), `IsFlagTraj` (off a flag the
  symbol is the proposal), `MClosed` (a marked set closed under the two rules), `UL` (an unmarked
  live data or second-coordinate reading);
* `UL.drvA` (an unmarked live reading is `A_t = F_R(D_{t-1})`), `one_cluster`, `card_marked_le`
  (at most `K` providers with a marked parent), `card_failed_le` (at most `K = q - h` failed
  checks), `ul_of_good`;
* **`coh_rel`** (the induction on the provider separation; base: the common proposal off flags for
  equal positions, the overlap `2h - q = 3K` of checked-provider sets for Moore neighbours),
  **`coherence_eq`**, **`coherence_compat`**, `coh_back` (`V_t + Mo ⊆ V_{t-1}`, labels persist),
  `coh_persist`, `coh_cover`, **`coherent_chart`** (one full legal time-constant chart);
* `markedFrom` (`𝓜^{t₀}`), `marked` (`𝓜`), **`marked_closed`** (so Lemma 5.3 applies to `𝓜`);
* the automaton: **`isFlagTraj_of_complete`** (a complete trajectory of `ruleCA CD s`, decoded to
  `ℤ² × ℤ⁴`, is a flagged trajectory with the flags of its noise), and **`coherence_complete`**
  (Lemma 5.3 for the complete trajectories of the automaton and the raw marked set `𝓜`).
-/
import UncomputableNoiseDiagram.Rule.Noise
import UncomputableNoiseDiagram.PCA.Pullback

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UND.Coh

open UND.Rule
open FNE (Plane box mooreDirs)

/-! ## Providers paired by a unit shift -/

/-- The source of the pairing (13): a cluster, the shifted block coordinate in `{0, …, 14}` and
the other three block coordinates. -/
abbrev PSrc := Option (Fin 4) × Fin 15 × (Fin 3 → Fin 16)

theorem card_PSrc : Fintype.card PSrc = 5 * 15 * 16 ^ 3 := by
  simp [Fintype.card_prod, Fintype.card_option]

/-- The upper provider of a pair: block coordinate `x + 1` at `j`. -/
def pHi (j : Fin 4) (s : PSrc) : Prov := (s.1, Fin.insertNth j s.2.1.succ s.2.2)

/-- The lower provider of a pair: block coordinate `x` at `j`. -/
def pLo (j : Fin 4) (s : PSrc) : Prov := (s.1, Fin.insertNth j s.2.1.castSucc s.2.2)

theorem insertNth_inj {j : Fin 4} {x x' : Fin 16} {r r' : Fin 3 → Fin 16}
    (h : (Fin.insertNth j x r : Fin 4 → Fin 16) = Fin.insertNth j x' r') : x = x' ∧ r = r' := by
  refine ⟨?_, funext fun i => ?_⟩
  · have := congrFun h j
    rwa [Fin.insertNth_apply_same, Fin.insertNth_apply_same] at this
  · have := congrFun h (j.succAbove i)
    rwa [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove] at this

theorem pHi_injective (j : Fin 4) : Function.Injective (pHi j) := by
  rintro ⟨c, x, r⟩ ⟨c', x', r'⟩ h
  simp only [pHi, Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  obtain ⟨hx, rfl⟩ := insertNth_inj h2
  rw [Fin.succ_inj.1 hx]

theorem pLo_injective (j : Fin 4) : Function.Injective (pLo j) := by
  rintro ⟨c, x, r⟩ ⟨c', x', r'⟩ h
  simp only [pLo, Prod.mk.injEq] at h
  obtain ⟨rfl, h2⟩ := h
  obtain ⟨hx, rfl⟩ := insertNth_inj h2
  rw [Fin.castSucc_inj.1 hx]

/-- The two providers of a pair differ by the unit vector `e_j`. -/
theorem provOff_pair (j : Fin 4) (s : PSrc) (i : Fin 4) :
    provOff (pHi j s) i = provOff (pLo j s) i + if i = j then 1 else 0 := by
  simp only [provOff, pHi, pLo, Pi.add_apply]
  by_cases hi : i = j
  · subst hi
    rw [Fin.insertNth_apply_same, Fin.insertNth_apply_same, ite_eq_left rfl, Fin.val_succ,
      Fin.val_castSucc]
    push_cast; ring
  · obtain ⟨i', rfl⟩ := Fin.exists_succAbove_eq hi
    rw [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_succAbove, ite_eq_right hi, add_zero]

/-- **The pairing count** (13): if at most `|Bad₁| + |Bad₂| < 5·15·16³` providers are discarded on
the two sides, some pair survives. -/
theorem exists_pair (f1 f2 : PSrc → Prov) (h1 : Function.Injective f1)
    (h2 : Function.Injective f2) (Bad1 Bad2 : Finset Prov)
    (h : Bad1.card + Bad2.card < 5 * 15 * 16 ^ 3) : ∃ s, f1 s ∉ Bad1 ∧ f2 s ∉ Bad2 := by
  classical
  by_contra hc
  push Not at hc
  have hA : (Finset.univ.filter fun s => f1 s ∈ Bad1).card ≤ Bad1.card :=
    Finset.card_le_card_of_injOn f1 (fun s hs => (Finset.mem_filter.1 hs).2)
      (fun a _ b _ e => h1 e)
  have hB : (Finset.univ.filter fun s => f2 s ∈ Bad2).card ≤ Bad2.card :=
    Finset.card_le_card_of_injOn f2 (fun s hs => (Finset.mem_filter.1 hs).2)
      (fun a _ b _ e => h2 e)
  have hU : (Finset.univ : Finset PSrc) ⊆ (Finset.univ.filter fun s => f1 s ∈ Bad1) ∪
      (Finset.univ.filter fun s => f2 s ∈ Bad2) := by
    intro s _
    by_cases hs : f1 s ∈ Bad1
    · exact Finset.mem_union_left _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hs⟩)
    · exact Finset.mem_union_right _ (Finset.mem_filter.2 ⟨Finset.mem_univ _, hc s hs⟩)
  have := (Finset.card_le_card hU).trans (Finset.card_union_le _ _)
  rw [Finset.card_univ, card_PSrc] at this
  omega

/-! ## Provider separation -/

/-- The provider separation `‖P' - P‖₁`. -/
def sep (P P' : Fin 4 → ℤ) : ℕ := ∑ i, (P' i - P i).natAbs

theorem sep_zero {P P' : Fin 4 → ℤ} (h : sep P P' = 0) : P = P' := by
  funext i
  have := (Finset.sum_eq_zero_iff.1 h) i (Finset.mem_univ _)
  omega

theorem sep_step {P P' : Fin 4 → ℤ} {j : Fin 4} (o o' : Fin 4 → ℤ)
    (ho : ∀ i, o' i = o i - if i = j then Int.sign (P' j - P j) else 0) (hj : P j ≠ P' j) :
    sep (P + o) (P' + o') + 1 = sep P P' := by
  have key : ∀ i, ((P' + o') i - (P + o) i).natAbs + (if i = j then 1 else 0) =
      (P' i - P i).natAbs := by
    intro i
    simp only [Pi.add_apply, ho]
    by_cases hi : i = j
    · subst hi
      simp only [↓reduceIte]
      rcases lt_or_gt_of_ne hj with h | h
      · rw [Int.sign_eq_one_of_pos (by omega)]; omega
      · rw [Int.sign_eq_neg_one_of_neg (by omega)]; omega
    · simp only [hi, ↓reduceIte]; omega
  simp only [sep]
  rw [← Finset.sum_congr rfl fun i _ => key i, Finset.sum_add_distrib, Finset.sum_ite_eq']
  simp


/-! ## Trajectories, replacement flags and marked sets -/

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] (CD : ChartData B τ)

/-- `M` marks a Moore parent of `w` through the provider `π`: a site of the planar box around
`w.1` at the provider coordinate `w.2 + provOff π`. -/
def MarkedAt (M : ISite → Prop) (w : ISite) (π : Prov) : Prop :=
  ∃ μ ∈ box 1, M (w.1 + μ, w.2 + provOff π)

/-- Marked Moore parents in two distinct provider clusters. -/
def TwoCl (M : ISite → Prop) (w : ISite) : Prop :=
  ∃ π π' : Prov, π.1 ≠ π'.1 ∧ MarkedAt M w π ∧ MarkedAt M w π'

/-- A trajectory of (6) with replacement flags `E` (decoded): off a flag the symbol is the
proposal of the previous configuration. -/
def IsFlagTraj (s : ℕ) (X : ℤ → PConfig CD) (E : ℤ → ISite → Prop) : Prop :=
  ∀ t w, ¬ E t w → X t w = proposal s (X (t - 1)) w

/-- A marked set closed under the two rules of `𝓜`: replacement flags are marked, and so is every
site with marked Moore parents in two distinct provider clusters. -/
def MClosed (E M : ℤ → ISite → Prop) : Prop :=
  ∀ t w, (E t w ∨ TwoCl (M (t - 1)) w) → M t w

/-- An unmarked live data or second-coordinate reading of `a` at `(w, t)`. -/
def UL (X : ℤ → PConfig CD) (M : ℤ → ISite → Prop) (t : ℤ) (w : ISite)
    (a : LiveLetter CD.toWangRel) : Prop :=
  ¬ M t w ∧ ((X t w).1 = some a ∨ (X t w).2.1 = some a)

/-- The relation of Lemma 5.3 at a planar displacement `μ ∈ Mo`: equal letters for `μ = 0`,
compatible letters otherwise. -/
def Rel (μ : Plane) (a a' : LiveLetter CD.toWangRel) : Prop :=
  (μ = 0 → a = a') ∧ (μ ≠ 0 → Compatible CD.toWangRel a a' μ)

variable {CD} {s : ℕ} {X : ℤ → PConfig CD} {E M : ℤ → ISite → Prop}

/-- An unmarked live reading is the checker's output `A_t(w) = F_R(D_{t-1})(w)`. -/
theorem UL.drvA (hX : IsFlagTraj CD s X E) (hM : MClosed E M) {t : ℤ} {w : ISite}
    {a : LiveLetter CD.toWangRel} (h : UL CD X M t w a) : drvA (X (t - 1)) w = some a := by
  have hE : ¬ E t w := fun hE => h.1 (hM t w (Or.inl hE))
  have hx := hX t w hE
  rcases h.2 with h2 | h2
  · rw [hx] at h2
    simp only [proposal] at h2
    split_ifs at h2
    exact h2
  · rw [hx] at h2
    exact h2

/-- An unmarked site has its marked Moore parents in at most one cluster. -/
theorem one_cluster (hM : MClosed E M) {t : ℤ} {w : ISite} (h : ¬ M t w) :
    ∃ c : Option (Fin 4), ∀ π, MarkedAt (M (t - 1)) w π → π.1 = c := by
  by_cases hex : ∃ π, MarkedAt (M (t - 1)) w π
  · obtain ⟨π0, h0⟩ := hex
    refine ⟨π0.1, fun π hπ => ?_⟩
    by_contra hne
    exact h (hM t w (Or.inr ⟨π, π0, hne, hπ, h0⟩))
  · exact ⟨none, fun π hπ => absurd ⟨π, hπ⟩ hex⟩

theorem card_cluster (c : Option (Fin 4)) :
    (Finset.univ.filter fun π : Prov => π.1 = c).card = UND.Param.K := by
  have e : (Finset.univ.filter fun π : Prov => π.1 = c) = {c} ×ˢ Finset.univ := by
    ext π
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_product,
      Finset.mem_singleton, and_true]
  rw [e, Finset.card_product, Finset.card_singleton, Finset.card_univ]
  simp [UND.Param.K]

open Classical in
/-- At most `K` providers of an unmarked site have a marked Moore parent. -/
theorem card_marked_le (hM : MClosed E M) {t : ℤ} {w : ISite} (h : ¬ M t w) :
    (Finset.univ.filter fun π => MarkedAt (M (t - 1)) w π).card ≤ UND.Param.K := by
  obtain ⟨c, hc⟩ := one_cluster hM h
  rw [← card_cluster c]
  exact Finset.card_le_card fun π hπ =>
    Finset.mem_filter.2 ⟨Finset.mem_univ _, hc π (Finset.mem_filter.1 hπ).2⟩

/-- At most `K = q - h` checked providers of a live output fail to read its letter. -/
theorem card_failed_le {D : ISite → ChartSym CD.toWangRel} {u : Plane} {P : Fin 4 → ℤ}
    {a : LiveLetter CD.toWangRel} (h : FR CD.toWangRel D (u, P) = some a) :
    (Finset.univ.filter fun π : Prov =>
      ¬ chk CD.toWangRel (fun v => D (v, P + provOff π)) u = some a).card ≤ UND.Param.K := by
  rw [FR_eq_some_iff] at h
  have h' : UND.Param.h ≤ (Finset.univ.filter fun π : Prov =>
      chk CD.toWangRel (fun v => D (v, P + provOff π)) u = some a).card := h
  have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Prov))
    (fun π : Prov => chk CD.toWangRel (fun v => D (v, P + provOff π)) u = some a)
  rw [Finset.card_univ, card_Prov] at this
  simp only [UND.Param.q, UND.Param.h] at this h'
  omega

/-- A provider that reads `a` and has no marked Moore parent supplies an unmarked live data
reading of `a` one update earlier. -/
theorem ul_of_good {t : ℤ} {u : Plane} {P : Fin 4 → ℤ} {π : Prov} {a : LiveLetter CD.toWangRel}
    (hchk : chk CD.toWangRel (fun v => dataOf (X (t - 1)) (v, P + provOff π)) u = some a)
    (hm : ¬ MarkedAt (M (t - 1)) (u, P) π) : UL CD X M (t - 1) (u, P + provOff π) a := by
  refine ⟨fun hM' => hm ⟨0, by simp [box], by simpa using hM'⟩, Or.inl ?_⟩
  simp only [chk] at hchk
  split_ifs at hchk
  exact hchk

/-- **The induction of Lemma 5.3** on the provider separation: unmarked live readings at one time,
at planar displacement `μ ∈ Mo`, are equal (`μ = 0`) or compatible (`μ ≠ 0`). -/
theorem coh_rel (hX : IsFlagTraj CD s X E) (hM : MClosed E M) (n : ℕ) :
    ∀ (t : ℤ) (u : Plane) (P P' : Fin 4 → ℤ) (μ : Plane) (a a' : LiveLetter CD.toWangRel),
      μ ∈ box 1 → sep P P' = n → UL CD X M t (u, P) a → UL CD X M t (u + μ, P') a' →
      Rel CD μ a a' := by
  classical
  induction n with
  | zero =>
    intro t u P P' μ a a' hμ hs h h'
    obtain rfl := sep_zero hs
    have hA := h.drvA hX hM
    have hA' := h'.drvA hX hM
    refine ⟨fun h0 => ?_, fun h0 => ?_⟩
    · subst h0
      rw [add_zero, hA] at hA'
      exact Option.some_injective _ hA'
    · rw [drvA, FR_eq_some_iff] at hA hA'
      have hQ1 : UND.Param.h ≤ (Finset.univ.filter fun π : Prov =>
          chk CD.toWangRel (fun v => dataOf (X (t - 1)) (v, P + provOff π)) u = some a).card :=
        hA
      have hQ2 : UND.Param.h ≤ (Finset.univ.filter fun π : Prov =>
          chk CD.toWangRel (fun v => dataOf (X (t - 1)) (v, P + provOff π)) (u + μ) =
            some a').card := hA'
      have hq := UND.Param.q_lt_two_h
      obtain ⟨π, hπ⟩ := Finset.inter_nonempty_of_card_lt_card_add_card (s := Finset.univ)
        (t := Finset.univ.filter fun π : Prov =>
          chk CD.toWangRel (fun v => dataOf (X (t - 1)) (v, P + provOff π)) u = some a)
        (u := Finset.univ.filter fun π : Prov =>
          chk CD.toWangRel (fun v => dataOf (X (t - 1)) (v, P + provOff π)) (u + μ) = some a')
        (Finset.subset_univ _) (Finset.subset_univ _) (by rw [Finset.card_univ, card_Prov]; omega)
      rw [Finset.mem_inter, Finset.mem_filter, Finset.mem_filter] at hπ
      obtain ⟨⟨-, c1⟩, ⟨-, c2⟩⟩ := hπ
      simp only [chk] at c1 c2
      split_ifs at c1 c2 with k1 k2
      obtain ⟨b, hb, hall⟩ := k1
      have hba : b = a := Option.some_injective _ (hb.symm.trans c1)
      subst hba
      obtain ⟨b', hb', hc⟩ := hall μ (Finset.mem_erase.2 ⟨h0, hμ⟩)
      have hb'' : dataOf (X (t - 1)) (u + μ, P + provOff π) = some b' := hb'
      rw [c2] at hb''
      rw [Option.some_injective _ hb'']
      exact hc
  | succ n ih =>
    intro t u P P' μ a a' hμ hs h h'
    have hne : P ≠ P' := by
      rintro rfl
      simp [sep] at hs
    obtain ⟨j, hj⟩ : ∃ j, P j ≠ P' j := by
      by_contra hc
      push Not at hc
      exact hne (funext hc)
    have hA := h.drvA hX hM
    have hA' := h'.drvA hX hM
    have hf1 := card_failed_le hA
    have hf2 := card_failed_le hA'
    have hm1 := card_marked_le hM h.1
    have hm2 := card_marked_le hM h'.1
    set Bad1 := (Finset.univ.filter fun π : Prov =>
        ¬ chk CD.toWangRel (fun v => dataOf (X (t - 1)) (v, P + provOff π)) u = some a) ∪
      (Finset.univ.filter fun π => MarkedAt (M (t - 1)) (u, P) π) with hB1
    set Bad2 := (Finset.univ.filter fun π : Prov =>
        ¬ chk CD.toWangRel (fun v => dataOf (X (t - 1)) (v, P' + provOff π)) (u + μ) =
          some a') ∪
      (Finset.univ.filter fun π => MarkedAt (M (t - 1)) (u + μ, P') π) with hB2
    have hc1 : Bad1.card ≤ 2 * UND.Param.K :=
      (Finset.card_union_le _ _).trans (by omega)
    have hc2 : Bad2.card ≤ 2 * UND.Param.K :=
      (Finset.card_union_le _ _).trans (by omega)
    have hK : UND.Param.K = 65536 := by norm_num [UND.Param.K]
    have hcard : Bad1.card + Bad2.card < 5 * 15 * 16 ^ 3 := by omega
    have good1 : ∀ π, π ∉ Bad1 → UL CD X M (t - 1) (u, P + provOff π) a := fun π hπ => by
      simp only [hB1, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        not_or, not_not] at hπ
      exact ul_of_good hπ.1 hπ.2
    have good2 : ∀ π, π ∉ Bad2 → UL CD X M (t - 1) (u + μ, P' + provOff π) a' := fun π hπ => by
      simp only [hB2, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and,
        not_or, not_not] at hπ
      exact ul_of_good hπ.1 hπ.2
    by_cases hdir : P j < P' j
    · obtain ⟨σ, hσ1, hσ2⟩ := exists_pair (pHi j) (pLo j) (pHi_injective j) (pLo_injective j)
        Bad1 Bad2 hcard
      have hstep := sep_step (P := P) (P' := P') (provOff (pHi j σ)) (provOff (pLo j σ))
        (fun i => by
          rw [provOff_pair j σ i, Int.sign_eq_one_of_pos (by omega)]
          split_ifs <;> ring) hj
      exact ih (t - 1) u _ _ μ a a' hμ (by omega) (good1 _ hσ1) (good2 _ hσ2)
    · obtain ⟨σ, hσ1, hσ2⟩ := exists_pair (pLo j) (pHi j) (pLo_injective j) (pHi_injective j)
        Bad1 Bad2 hcard
      have hstep := sep_step (P := P) (P' := P') (provOff (pLo j σ)) (provOff (pHi j σ))
        (fun i => by
          rw [provOff_pair j σ i, Int.sign_eq_neg_one_of_neg (by omega)]
          split_ifs <;> ring) hj
      exact ih (t - 1) u _ _ μ a a' hμ (by omega) (good1 _ hσ1) (good2 _ hσ2)

/-- **Lemma 5.3, first assertion**: in every trajectory, all unmarked live data or
second-coordinate readings at a fixed planar site and time have the same letter over all provider
positions. -/
theorem coherence_eq (hX : IsFlagTraj CD s X E) (hM : MClosed E M) {t : ℤ} {u : Plane}
    {P P' : Fin 4 → ℤ} {a a' : LiveLetter CD.toWangRel} (h : UL CD X M t (u, P) a)
    (h' : UL CD X M t (u, P') a') : a = a' :=
  (coh_rel hX hM _ t u P P' 0 a a' (by simp [box]) rfl h (by rwa [add_zero])).1 rfl

/-- **Lemma 5.3, second assertion**: readings at neighbouring planar sites are compatible in all
eight Moore directions. -/
theorem coherence_compat (hX : IsFlagTraj CD s X E) (hM : MClosed E M) {t : ℤ} {u d : Plane}
    {P P' : Fin 4 → ℤ} {a a' : LiveLetter CD.toWangRel} (hd : d ∈ mooreDirs)
    (h : UL CD X M t (u, P) a) (h' : UL CD X M t (u + d, P') a') :
    Compatible CD.toWangRel a a' d :=
  (coh_rel hX hM _ t u P P' d a a' (Finset.mem_of_mem_erase hd) rfl h h').2
    (Finset.ne_of_mem_erase hd)

/-- `V_t + Mo ⊆ V_{t-1}`, with the label persisting at the centre. -/
theorem coh_back (hX : IsFlagTraj CD s X E) (hM : MClosed E M) {t : ℤ} {u : Plane}
    {P : Fin 4 → ℤ} {a : LiveLetter CD.toWangRel} (h : UL CD X M t (u, P) a) :
    ∃ P', ∀ μ ∈ box 1, ∃ a', UL CD X M (t - 1) (u + μ, P') a' ∧ (μ = 0 → a' = a) := by
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
  refine ⟨P + provOff π, fun μ hμ => ?_⟩
  have c1 := hπ1.2
  simp only [chk] at c1
  split_ifs at c1 with k1
  by_cases h0 : μ = 0
  · subst h0
    refine ⟨a, ?_, fun _ => rfl⟩
    rw [add_zero]
    refine ⟨fun hc => hπ2' ⟨0, by simp [box], by simpa using hc⟩, Or.inl c1⟩
  · obtain ⟨b, hb, hall⟩ := k1
    obtain ⟨b', hb', -⟩ := hall μ (Finset.mem_erase.2 ⟨h0, hμ⟩)
    exact ⟨b', ⟨fun hc => hπ2' ⟨μ, hμ, hc⟩, Or.inl hb'⟩, fun h0' => absurd h0' h0⟩

/-- Labels persist backwards: an unmarked live reading of `a` at time `t` gives one at every
earlier time, at the same planar site. -/
theorem coh_persist (hX : IsFlagTraj CD s X E) (hM : MClosed E M) {t : ℤ} {u : Plane}
    {P : Fin 4 → ℤ} {a : LiveLetter CD.toWangRel} (h : UL CD X M t (u, P) a) (k : ℕ) :
    ∃ P', UL CD X M (t - k) (u, P') a := by
  induction k with
  | zero => exact ⟨P, by simpa using h⟩
  | succ k ih =>
    obtain ⟨P1, h1⟩ := ih
    obtain ⟨P2, h2⟩ := coh_back hX hM h1
    obtain ⟨a', h3, h4⟩ := h2 0 (by simp [box])
    rw [h4 rfl, add_zero] at h3
    refine ⟨P2, ?_⟩
    rwa [show t - ((k + 1 : ℕ) : ℤ) = t - k - 1 by push_cast; ring]

theorem step_toward (d : ℤ) (k : ℕ) (h : d.natAbs ≤ k + 1) :
    (d - d.sign).natAbs ≤ k ∧ -1 ≤ d.sign ∧ d.sign ≤ 1 := by
  rcases lt_trichotomy d 0 with hd | hd | hd
  · rw [Int.sign_eq_neg_one_of_neg hd]; omega
  · subst hd; simp
  · rw [Int.sign_eq_one_of_pos hd]; omega

/-- A nonempty `V_t` expands: every planar site within Chebyshev distance `k` of an unmarked live
reading at time `t₀` has an unmarked live reading at time `t₀ - k`. -/
theorem coh_cover (hX : IsFlagTraj CD s X E) (hM : MClosed E M) {t0 : ℤ} {u0 : Plane}
    {P0 : Fin 4 → ℤ} {a0 : LiveLetter CD.toWangRel} (h : UL CD X M t0 (u0, P0) a0) (k : ℕ) :
    ∀ u : Plane, (u.1 - u0.1).natAbs ≤ k → (u.2 - u0.2).natAbs ≤ k →
      ∃ P a, UL CD X M (t0 - k) (u, P) a := by
  induction k with
  | zero =>
    intro u h1 h2
    have e : u = u0 := Prod.ext (by omega) (by omega)
    subst e
    exact ⟨P0, a0, by simpa using h⟩
  | succ k ih =>
    intro u h1 h2
    obtain ⟨s1, l1, r1⟩ := step_toward (u.1 - u0.1) k h1
    obtain ⟨s2, l2, r2⟩ := step_toward (u.2 - u0.2) k h2
    set μ : Plane := ((u.1 - u0.1).sign, (u.2 - u0.2).sign) with hμ
    obtain ⟨P, a, hP⟩ := ih (u - μ) (by simp only [hμ, Prod.fst_sub]; omega)
      (by simp only [hμ, Prod.snd_sub]; omega)
    obtain ⟨P', hP'⟩ := coh_back hX hM hP
    obtain ⟨a', h3, -⟩ := hP' μ (by
      simp only [box, hμ, Finset.mem_product, Finset.mem_Icc]; omega)
    rw [sub_add_cancel] at h3
    exact ⟨P', a', by rwa [show t0 - ((k + 1 : ℕ) : ℤ) = t0 - k - 1 by push_cast; ring]⟩

/-- **Lemma 5.3, third assertion**: if any unmarked live reading exists, one full legal,
time-constant planar chart agrees with every unmarked live reading at every time. -/
theorem coherent_chart (hX : IsFlagTraj CD s X E) (hM : MClosed E M)
    (hne : ∃ t w a, UL CD X M t w a) :
    ∃ c : Plane → LiveLetter CD.toWangRel, IsFullChart CD.toWangRel c ∧
      ∀ t u P a, UL CD X M t (u, P) a → c u = a := by
  classical
  obtain ⟨t0, ⟨u0, P0⟩, a0, h0⟩ := hne
  have hex : ∀ u, ∃ a, ∃ t P, UL CD X M t (u, P) a := fun u => by
    obtain ⟨P, a, h⟩ := coh_cover hX hM h0 (max (u.1 - u0.1).natAbs (u.2 - u0.2).natAbs) u
      (le_max_left _ _) (le_max_right _ _)
    exact ⟨a, _, P, h⟩
  have hdown : ∀ {t t' u P a}, UL CD X M t (u, P) a → t' ≤ t → ∃ P', UL CD X M t' (u, P') a := by
    intro t t' u P a h hle
    obtain ⟨P1, h1⟩ := coh_persist hX hM h (t - t').toNat
    exact ⟨P1, by rwa [show t - ((t - t').toNat : ℤ) = t' by omega] at h1⟩
  have hsame : ∀ {t t' u P P' a a'}, UL CD X M t (u, P) a → UL CD X M t' (u, P') a' → a = a' := by
    intro t t' u P P' a a' h h'
    obtain ⟨P1, h1⟩ := hdown h (min_le_left t t')
    obtain ⟨P2, h2⟩ := hdown h' (min_le_right t t')
    exact coherence_eq hX hM h1 h2
  refine ⟨fun u => (hex u).choose, fun u d hd => ?_, fun t u P a h => ?_⟩
  · obtain ⟨t1, P1, h1⟩ := (hex u).choose_spec
    obtain ⟨t2, P2, h2⟩ := (hex (u + d)).choose_spec
    obtain ⟨Q1, g1⟩ := hdown h1 (min_le_left t1 t2)
    obtain ⟨Q2, g2⟩ := hdown h2 (min_le_right t1 t2)
    exact coherence_compat hX hM hd g1 g2
  · obtain ⟨t1, P1, h1⟩ := (hex u).choose_spec
    exact hsame h1 h

/-! ## The raw marked set `𝓜` -/

/-- `𝓜^{t₀}` at time `t₀ + n`: empty at `t₀`; then each replacement flag and each site having a
marked Moore parent in two distinct provider clusters. -/
def markedFrom (E : ℤ → ISite → Prop) (t0 : ℤ) : ℕ → ISite → Prop
  | 0 => fun _ => False
  | n + 1 => fun w => E (t0 + (n + 1 : ℕ)) w ∨ TwoCl (markedFrom E t0 n) w

/-- **`𝓜`**: the increasing limit of `𝓜^{t₀}` as `t₀ → -∞` (membership has a finite derivation;
it is determined by the flags alone). -/
def marked (E : ℤ → ISite → Prop) (t : ℤ) (w : ISite) : Prop :=
  ∃ n : ℕ, markedFrom E (t - n) n w

theorem markedAt_mono {M M' : ISite → Prop} (h : ∀ w, M w → M' w) {w : ISite} {π : Prov}
    (hm : MarkedAt M w π) : MarkedAt M' w π := by
  obtain ⟨μ, hμ, hm⟩ := hm
  exact ⟨μ, hμ, h _ hm⟩

theorem twoCl_mono {M M' : ISite → Prop} (h : ∀ w, M w → M' w) {w : ISite} (hm : TwoCl M w) :
    TwoCl M' w := by
  obtain ⟨π, π', hne, h1, h2⟩ := hm
  exact ⟨π, π', hne, markedAt_mono h h1, markedAt_mono h h2⟩

/-- An earlier start marks more: `𝓜^{t₀} ⊆ 𝓜^{t₀ - 1}`. -/
theorem markedFrom_mono (E : ℤ → ISite → Prop) (t0 : ℤ) (n : ℕ) :
    ∀ w, markedFrom E t0 n w → markedFrom E (t0 - 1) (n + 1) w := by
  induction n with
  | zero => intro w h; exact h.elim
  | succ n ih =>
    intro w h
    rcases h with h | h
    · left
      have e : t0 - 1 + ((n + 1 + 1 : ℕ) : ℤ) = t0 + ((n + 1 : ℕ) : ℤ) := by push_cast; ring
      rw [e]; exact h
    · exact Or.inr (twoCl_mono ih h)

theorem markedFrom_mono' (E : ℤ → ISite → Prop) (t0 : ℤ) (n k : ℕ) (w : ISite)
    (h : markedFrom E t0 n w) : markedFrom E (t0 - k) (n + k) w := by
  induction k with
  | zero => simpa using h
  | succ k ih =>
    have := markedFrom_mono E (t0 - k) (n + k) w ih
    rwa [show t0 - (k : ℤ) - 1 = t0 - ((k + 1 : ℕ) : ℤ) by push_cast; ring,
      show n + k + 1 = n + (k + 1) by ring] at this

/-- **`𝓜` is closed under its two rules**, so Lemma 5.3 applies to it. -/
theorem marked_closed (E : ℤ → ISite → Prop) : MClosed E (marked E) := by
  intro t w h
  rcases h with h | h
  · refine ⟨1, Or.inl ?_⟩
    rwa [show t - ((1 : ℕ) : ℤ) + ((0 + 1 : ℕ) : ℤ) = t by push_cast; ring]
  · obtain ⟨π, π', hne, ⟨μ, hμ, n1, h1⟩, ⟨μ', hμ', n2, h2⟩⟩ := h
    set N := max n1 n2
    have g1 := markedFrom_mono' E _ _ (N - n1) _ h1
    have g2 := markedFrom_mono' E _ _ (N - n2) _ h2
    rw [show t - 1 - (n1 : ℤ) - ((N - n1 : ℕ) : ℤ) = t - 1 - N by omega,
      show n1 + (N - n1) = N by omega] at g1
    rw [show t - 1 - (n2 : ℤ) - ((N - n2 : ℕ) : ℤ) = t - 1 - N by omega,
      show n2 + (N - n2) = N by omega] at g2
    refine ⟨N + 1, Or.inr ⟨π, π', hne, ⟨μ, hμ, ?_⟩, ⟨μ', hμ', ?_⟩⟩⟩
    · rwa [show t - ((N + 1 : ℕ) : ℤ) = t - 1 - N by push_cast; ring]
    · rwa [show t - ((N + 1 : ℕ) : ℤ) = t - 1 - N by push_cast; ring]

/-! ## Complete trajectories of the automaton -/

/-- The replacement flags of a two-sided noise, read on `ℤ² × ℤ⁴`. -/
def flagsOf {A : UND.CA 6} (ω : A.Noise₂) (t : ℤ) (w : ISite) : Prop :=
  (ω (t, siteEquiv.symm w)).1 = true

/-- **A complete trajectory of the automaton (6), decoded, is a flagged trajectory** with the flags
of its noise (`B ≥ 1`). -/
theorem isFlagTraj_of_complete (CD : ChartData B τ) (s : ℕ) (hB : 1 ≤ B)
    {ω : (ruleCA CD s).Noise₂} {X : ℤ → (ruleCA CD s).Config}
    (hX : (ruleCA CD s).IsComplete ω X) :
    IsFlagTraj CD s (fun t => decodeConfig (X t)) (flagsOf ω) := by
  intro t w hE
  have h := hX (t - 1)
  rw [sub_add_cancel] at h
  have key := congrFun (update_decode (proposal (CD := CD) s) (nbhdP B)
    (fun x a => proposal_translate s x a) (fun _ _ _ hh => proposal_local s hB hh)
    (fun v => ω (t, v)) (X (t - 1))) w
  show decodeConfig (X t) w = proposal s (decodeConfig (X (t - 1))) w
  rw [h]
  refine key.trans ?_
  exact ite_eq_right hE

/-- **Lemma 5.3 for the automaton**: in every complete trajectory of (6), with the raw marked set
`𝓜` of its noise, unmarked live readings at one planar site and time agree over all provider
positions, readings at Moore-neighbour sites are compatible, and if any exists one full legal
time-constant chart agrees with all of them. -/
theorem coherence_complete (CD : ChartData B τ) (s : ℕ) (hB : 1 ≤ B)
    {ω : (ruleCA CD s).Noise₂} {X : ℤ → (ruleCA CD s).Config}
    (hX : (ruleCA CD s).IsComplete ω X) :
    (∀ t u P P' a a', UL CD (fun t => decodeConfig (X t)) (marked (flagsOf ω)) t (u, P) a →
      UL CD (fun t => decodeConfig (X t)) (marked (flagsOf ω)) t (u, P') a' → a = a') ∧
    (∀ t u d P P' a a', d ∈ mooreDirs →
      UL CD (fun t => decodeConfig (X t)) (marked (flagsOf ω)) t (u, P) a →
      UL CD (fun t => decodeConfig (X t)) (marked (flagsOf ω)) t (u + d, P') a' →
      Compatible CD.toWangRel a a' d) ∧
    ((∃ t w a, UL CD (fun t => decodeConfig (X t)) (marked (flagsOf ω)) t w a) →
      ∃ c : Plane → LiveLetter CD.toWangRel, IsFullChart CD.toWangRel c ∧
        ∀ t u P a, UL CD (fun t => decodeConfig (X t)) (marked (flagsOf ω)) t (u, P) a →
          c u = a) := by
  have hF := isFlagTraj_of_complete CD s hB hX
  have hM := marked_closed (flagsOf ω)
  exact ⟨fun _ _ _ _ _ _ h h' => coherence_eq hF hM h h',
    fun _ _ _ _ _ _ _ hd h h' => coherence_compat hF hM hd h h', coherent_chart hF hM⟩

end UND.Coh
