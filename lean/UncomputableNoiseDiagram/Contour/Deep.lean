/-
# Lemma 5.4 (deep wrong readings) (C4)

Node C4 of `BLUEPRINT.md` (Part A.5). NEW: the second concrete instance of Lemma 5.1
(`Contour/Grouped.lean`), on the virtual levels of a deep query stacked on the marked derivation.

Paper (Lemma 5.4): "Relative to the chart in Lemma 5.3, a wrong live depth-`T` query in (3) has a
finite contour with at least eleven distinct raw flags and at most `50(f-1)` support edges. All its
flags are no later than the queried input time. At lag `ℓ ≤ W` from a current output time `t`, its
earliest flag time `t₀` satisfies `t - t₀ ≤ W + 50(f-1)`."
Proof: "Every wrong live actual reading is marked by Lemma 5.3. A wrong live forecast retains its
letter at at least `h` center providers. At each of its `T` virtual levels these wrong centers
occupy two distinct clusters; append their finite marked derivations. Give a virtual
`F_R^j(D_s)(u,P)` the provider characteristic coordinate `P + vs + jv`, and actual `D_s(u,P)` the
coordinate `P + vs`. Every virtual support has displacement `s' - v`, `s' ∈ S`, as does the final
step to actual data; its potentials are the five spatial potentials `5Σχ_{P,i}`, `-5χ_{P,i}`. The
gains are (11) and `-715`. Recentring in (3) places the query root at the current characteristic
coordinate. Apply Lemma 5.1. Every root-to-flag arm crosses all `T` virtual levels, so
`e ≥ T = 500`, and `e ≤ 50(f-1)` gives `f ≥ 11`. Virtual levels precede no actual input flag in
physical time; their bookkeeping levels account for part of `e`. The remaining physical span is at
most `e`, and adding lag `ℓ` gives the stated bound."

Formalization.
* A vertex is `(y, j) : Pt × ℕ`: for `j = 0` the actual space-time point `y`; for `j ≥ 1` the
  virtual value `F_R^j(D_s)(y.1)` placed at the bookkeeping time `y.2 = s + j`. With the potentials
  of the bookkeeping point (`UND.Raw.psi`), `ψ₀ = 5Σχ`, `ψ_i = -5χ_i` for the characteristic
  coordinate `χ = P + v(s + j)`, exactly as printed; every support edge is a step `par` (virtual:
  centre providers; actual: Moore parents), so the gains are those of Lemma 5.2 (`psi_par`).
* The context `Ctx` (flags `E`, data `D` at time `s`, chart `c`); `depth` (the derivation depth of
  a marked point); binary vertices `NFv` (a wrong live virtual value) and `NFa` (a marked non-flag
  actual point); parents chosen by `Classical.epsilon` (`pdD`), two clusters (`exists_two_clusters`:
  `h > K` wrong centres occupy two clusters); the rank `rkD` (depth on actual points, one more than
  the supports on virtual levels); **`sysD`** (a `GroupedSystem`), **`isPotential_psiD`**.
* Reached vertices are wrong virtual values or marked actual points no later than `s` (`inv_reach`);
  reached terminals are flags no later than `s`; every root arm has at least `T` binary edges
  (`root_pBin_ge`).
* **`exists_deep_contour`** (Lemma 5.1 on `sysD`): if every wrong live actual reading at time `s`
  is marked, a wrong live value of `F_R^j(D_s)` (`j ≥ 1`) has a contour with `f` distinct flags,
  `85 e ≤ 4000(f - 1)`, `j ≤ e`, flags in `[s + j - e, s]`, at most `e` edges of the deep graph
  `nbrD` (degree `≤ 36q`) connected at the root.
* **`deep_wrong`** (Lemma 5.4): relative to a chart agreeing with every unmarked live reading, a
  wrong live deep query `Q_t(w)` has a contour with `f ≥ 11` distinct raw flags, `e ≤ 48(f - 1)
  ≤ 50(f - 1)` support edges, all flags no later than the queried input time `t - 1` and with
  `t - t₀ ≤ e`; **`deep_wrong_lag`**: at lag `ℓ ≤ W`, `t + ℓ - t₀ ≤ W + 50(f - 1)`.
-/
import UncomputableNoiseDiagram.Contour.RawPaths
import UncomputableNoiseDiagram.Rule.Proposal

set_option autoImplicit false
set_option linter.unusedSectionVars false
-- `DecidableEq (Sym2 (Pt × ℕ))` has instance size 150 (default limit 128)
set_option synthInstance.maxSize 512

noncomputable section

open Relation

namespace UND.Deep

open UND.Rule UND.Coh UND.Contour UND.Raw FNE.EdgeCount
open FNE (Plane box)

/-- Section 2.2: `T = 500`. -/
theorem T_eq : UND.Param.T = 500 := rfl

/- D21: `T` stays opaque below. -/
attribute [local irreducible] UND.Param.T

/-! ## Two clusters -/

/-- More than `K` providers occupy two distinct clusters. -/
theorem exists_two_clusters (S : Finset Prov) (hS : UND.Param.K < S.card) :
    ∃ π ∈ S, ∃ π' ∈ S, π.1 ≠ π'.1 := by
  classical
  obtain ⟨π, hπ⟩ : S.Nonempty := Finset.card_pos.mp (by omega)
  by_contra hc
  push Not at hc
  have hsub : S ⊆ Finset.univ.filter (fun π' : Prov => π'.1 = π.1) := fun π' hπ' =>
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, (hc π hπ π' hπ').symm⟩
  have := Finset.card_le_card hsub
  rw [card_cluster] at this
  omega

/-- Membership in a filter, for any decidability instance. -/
theorem prop_of_mem_filter' {α : Type*} {p : α → Prop} {S : Finset α} {inst : DecidablePred p}
    {a : α} (h : a ∈ @Finset.filter α p inst S) : p a :=
  ((@Finset.mem_filter α p inst S a).mp h).2

/-- A check returning a live letter returns the centre. -/
theorem chk_center {τ' : Type*} [Fintype τ'] [DecidableEq τ'] {R : WangRel τ'}
    {x : Plane → ChartSym R} {u : Plane} {a : LiveLetter R} (h : chk R x u = some a) :
    x u = some a := by
  unfold chk at h
  split_ifs at h
  exact h

/-! ## The context and the grouped support graph -/

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData B τ}

/-- The data of Lemma 5.4: flags `E`, the data `D = D_s` at the queried input time `s`, and the
chart `c` of Lemma 5.3. -/
structure Ctx (CD : ChartData B τ) where
  /-- replacement flags -/
  E : ℤ → ISite → Prop
  /-- the data at the queried input time -/
  D : ISite → ChartSym CD.toWangRel
  /-- the chart -/
  c : Plane → LiveLetter CD.toWangRel
  /-- the queried input time -/
  s : ℤ

namespace Ctx

variable (Γ : Ctx CD)

open Classical in
/-- The derivation depth of a marked point (`0` if unmarked). -/
def depth (y : Pt) : ℕ := if h : marked Γ.E y.2 y.1 then Nat.find h else 0

/-- A wrong live virtual value `F_R^j(D)(y.1) = a ≠ c(u)`. -/
def WrongV (y : Pt) (j : ℕ) : Prop :=
  ∃ a, (FR CD.toWangRel)^[j] Γ.D y.1 = some a ∧ a ≠ Γ.c y.1.1

/-- Binary virtual vertices: wrong live virtual values at bookkeeping time `s + j`. -/
def NFv (θ : Pt × ℕ) : Prop := 1 ≤ θ.2 ∧ θ.1.2 = Γ.s + θ.2 ∧ Γ.WrongV θ.1 θ.2

/-- Binary actual vertices: marked non-flag points. -/
def NFa (θ : Pt × ℕ) : Prop := θ.2 = 0 ∧ marked Γ.E θ.1.2 θ.1.1 ∧ ¬ Γ.E θ.1.2 θ.1.1

/-- An admissible support of `θ`. -/
def ChildOK (θ : Pt × ℕ) (y' : Pt) : Prop :=
  if θ.2 = 0 then marked Γ.E y'.2 y'.1 ∧ Γ.depth y' < Γ.depth θ.1
  else if θ.2 = 1 then marked Γ.E y'.2 y'.1 ∧ y'.2 ≤ Γ.s
  else Γ.NFv (y', θ.2 - 1)

/-- An admissible choice of two supports in distinct clusters. -/
def PGoodD (θ : Pt × ℕ) (d : (Prov × Plane) × (Prov × Plane)) : Prop :=
  d.1.1.1 ≠ d.2.1.1 ∧ d.1.2 ∈ box 1 ∧ d.2.2 ∈ box 1 ∧
    Γ.ChildOK θ (par θ.1 d.1.1 d.1.2) ∧ Γ.ChildOK θ (par θ.1 d.2.1 d.2.2)

/-- The chosen supports. -/
def pdD (θ : Pt × ℕ) : (Prov × Plane) × (Prov × Plane) := Classical.epsilon (Γ.PGoodD θ)

/-- The selected support `b`. -/
def selD (θ : Pt × ℕ) (b : Bool) : Prov × Plane := if b then (Γ.pdD θ).1 else (Γ.pdD θ).2

/-- The support vertex `b` of `θ`: one level down (actual points stay at level `0`). -/
def supD (θ : Pt × ℕ) (b : Bool) : Pt × ℕ := (par θ.1 (Γ.selD θ b).1 (Γ.selD θ b).2, θ.2 - 1)

/-- The rank: the derivation depth on actual points, one more than the supports on virtual
levels. -/
def rkD : ℕ → Pt → ℕ
  | 0, y => Γ.depth y
  | j + 1, y => 1 + max (rkD j (Γ.supD (y, j + 1) true).1) (rkD j (Γ.supD (y, j + 1) false).1)

theorem depth_spec {y : Pt} (h : marked Γ.E y.2 y.1) :
    markedFrom Γ.E (y.2 - Γ.depth y) (Γ.depth y) y.1 := by
  classical
  have e : Γ.depth y = Nat.find h := by unfold depth; rw [dite_eq_left h]
  rw [e]
  exact Nat.find_spec h

theorem depth_le {y : Pt} {n : ℕ} (h : markedFrom Γ.E (y.2 - n) n y.1) : Γ.depth y ≤ n := by
  classical
  have hm : marked Γ.E y.2 y.1 := ⟨n, h⟩
  have e : Γ.depth y = Nat.find hm := by unfold depth; rw [dite_eq_left hm]
  rw [e]
  exact Nat.find_min' hm h

variable {Γ}

theorem exists_pgoodD_a {θ : Pt × ℕ} (h : Γ.NFa θ) : ∃ d, Γ.PGoodD θ d := by
  obtain ⟨h0, hm, hE⟩ := h
  have hspec := Γ.depth_spec hm
  set n := Γ.depth θ.1 with hn
  obtain ⟨m, hm1⟩ : ∃ m, n = m + 1 := by
    rcases Nat.exists_eq_succ_of_ne_zero (n := n) (by
      intro h0'
      rw [h0'] at hspec
      exact hspec) with ⟨m, hm⟩
    exact ⟨m, hm⟩
  rw [hm1] at hspec
  rcases hspec with hspec | hspec
  · exact absurd (by rwa [show θ.1.2 - ((m + 1 : ℕ) : ℤ) + ((m + 1 : ℕ) : ℤ) = θ.1.2 by ring]
      at hspec) hE
  · obtain ⟨π, π', hne, ⟨μ, hμ, h1⟩, ⟨μ', hμ', h2⟩⟩ := hspec
    have key : ∀ (π : Prov) (μ : Plane),
        markedFrom Γ.E (θ.1.2 - ((m + 1 : ℕ) : ℤ)) m (θ.1.1.1 + μ, θ.1.1.2 + provOff π) →
        Γ.ChildOK θ (par θ.1 π μ) := by
      intro π μ hmf
      have hpm : markedFrom Γ.E ((par θ.1 π μ).2 - m) m (par θ.1 π μ).1 := by
        rw [par_time, show θ.1.2 - 1 - (m : ℤ) = θ.1.2 - ((m + 1 : ℕ) : ℤ) by push_cast; ring]
        exact hmf
      unfold ChildOK
      rw [ite_eq_left h0]
      exact ⟨⟨m, hpm⟩, by have := Γ.depth_le hpm; omega⟩
    exact ⟨((π, μ), (π', μ')), hne, hμ, hμ', key π μ h1, key π' μ' h2⟩

/-- Lemma 5.4's hypothesis "relative to the chart in Lemma 5.3": every wrong live actual reading
at the queried input time is marked. -/
def Good (Γ : Ctx CD) : Prop :=
  ∀ w a, Γ.D w = some a → a ≠ Γ.c w.1 → marked Γ.E Γ.s w

theorem zero_mem_box : (0 : Plane) ∈ box 1 := by
  simp [FNE.box]

/-- A wrong live virtual value has two wrong (or marked) supports in distinct clusters: "a wrong
live forecast retains its letter at at least `h` center providers … these wrong centers occupy two
distinct clusters". -/
theorem exists_pgoodD_v (hΓ : Γ.Good) {θ : Pt × ℕ} (h : Γ.NFv θ) : ∃ d, Γ.PGoodD θ d := by
  obtain ⟨h1, ht, a, ha, hne⟩ := h
  obtain ⟨i, hi⟩ : ∃ i, θ.2 = i + 1 := ⟨θ.2 - 1, by omega⟩
  rw [hi, Function.iterate_succ_apply', FR_eq_some_iff] at ha
  unfold quorumCount at ha
  have hS := exists_two_clusters _ (lt_of_lt_of_le (by norm_num [UND.Param.h, UND.Param.K]) ha)
  obtain ⟨π, hπ, π', hπ', hne'⟩ := hS
  have hp1 := prop_of_mem_filter' hπ
  have hp2 := prop_of_mem_filter' hπ'
  have hc1 := chk_center hp1
  have hc2 := chk_center hp2
  have key : ∀ π : Prov,
      ((FR CD.toWangRel)^[i] Γ.D) (θ.1.1.1, θ.1.1.2 + provOff π) = some a →
        Γ.ChildOK θ (par θ.1 π 0) := by
    intro π hπa
    have e1 : (par θ.1 π 0).1 = (θ.1.1.1, θ.1.1.2 + provOff π) := by simp [par]
    unfold ChildOK
    rw [ite_eq_right (show ¬ θ.2 = 0 by omega)]
    by_cases hi0 : i = 0
    · subst hi0
      rw [ite_eq_left (show θ.2 = 1 by omega)]
      have e2 : (par θ.1 π 0).2 = Γ.s := by rw [par_time, ht, hi]; push_cast; ring
      rw [e1, e2]
      exact ⟨hΓ _ a hπa hne, le_rfl⟩
    · rw [ite_eq_right (show ¬ θ.2 = 1 by omega)]
      refine ⟨by omega, ?_, a, ?_, ?_⟩
      · show (par θ.1 π 0).2 = Γ.s + ((θ.2 - 1 : ℕ) : ℤ)
        rw [par_time, ht]
        omega
      · show (FR CD.toWangRel)^[θ.2 - 1] Γ.D (par θ.1 π 0).1 = some a
        rw [e1, show θ.2 - 1 = i by omega]
        exact hπa
      · show a ≠ Γ.c (par θ.1 π 0).1.1
        rw [e1]
        exact hne
  exact ⟨((π, 0), (π', 0)), hne', zero_mem_box, zero_mem_box, key π hc1, key π' hc2⟩

theorem pdD_spec (hΓ : Γ.Good) {θ : Pt × ℕ} (h : Γ.NFv θ ∨ Γ.NFa θ) :
    Γ.PGoodD θ (Γ.pdD θ) := by
  rcases h with h | h
  · exact Classical.epsilon_spec (exists_pgoodD_v hΓ h)
  · exact Classical.epsilon_spec (exists_pgoodD_a h)

theorem childOK_sel (hΓ : Γ.Good) {θ : Pt × ℕ} (h : Γ.NFv θ ∨ Γ.NFa θ) (b : Bool) :
    Γ.ChildOK θ (Γ.supD θ b).1 ∧ (Γ.selD θ b).2 ∈ box 1 := by
  have := pdD_spec hΓ h
  cases b
  · exact ⟨this.2.2.2.2, this.2.2.1⟩
  · exact ⟨this.2.2.2.1, this.2.1⟩

theorem selD_ne (hΓ : Γ.Good) {θ : Pt × ℕ} (h : Γ.NFv θ ∨ Γ.NFa θ) :
    (Γ.selD θ true).1.1 ≠ (Γ.selD θ false).1.1 :=
  (pdD_spec hΓ h).1

/-- The rank decreases along supports (`NFa`: by the derivation depth; virtual: by definition). -/
theorem rk_supD {θ : Pt × ℕ} (h : Γ.NFv θ ∨ Γ.NFa θ) (b : Bool) :
    Γ.rkD (Γ.supD θ b).2 (Γ.supD θ b).1 < Γ.rkD θ.2 θ.1 := by
  obtain ⟨y, j⟩ := θ
  cases j with
  | zero =>
    have ha : Γ.NFa (y, 0) := h.resolve_left (fun hv => by have := hv.1; simp at this)
    have hp := Classical.epsilon_spec (exists_pgoodD_a ha)
    show Γ.depth (Γ.supD (y, 0) b).1 < Γ.depth y
    have hc : Γ.ChildOK (y, 0) (Γ.supD (y, 0) b).1 := by
      cases b
      · exact hp.2.2.2.2
      · exact hp.2.2.2.1
    unfold ChildOK at hc
    rw [ite_eq_left rfl] at hc
    exact hc.2
  | succ j =>
    show Γ.rkD j (Γ.supD (y, j + 1) b).1 <
      1 + max (Γ.rkD j (Γ.supD (y, j + 1) true).1) (Γ.rkD j (Γ.supD (y, j + 1) false).1)
    have h1 := le_max_left (Γ.rkD j (Γ.supD (y, j + 1) true).1)
      (Γ.rkD j (Γ.supD (y, j + 1) false).1)
    have h2 := le_max_right (Γ.rkD j (Γ.supD (y, j + 1) true).1)
      (Γ.rkD j (Γ.supD (y, j + 1) false).1)
    cases b <;> omega

variable (Γ) in
/-- **The deep contour graph** (Lemma 5.4): virtual levels stacked on the marked derivation.
Binary vertices are the wrong live virtual values and the marked non-flag actual points, with two
supports in distinct clusters; the good support of charge `c` lies in a cluster other than `c`; no
unary links; singleton groups. -/
def sysD : GroupedSystem (Pt × ℕ) (Option (Fin 4)) (Pt × ℕ) where
  rk θ := Γ.rkD θ.2 θ.1
  NF θ := Γ.NFv θ ∨ Γ.NFa θ
  UN _ := False
  not_UN_of_NF _ _ h := h
  sup := Γ.supD
  un θ := θ
  good c θ := decide ((Γ.selD θ true).1.1 ≠ c)
  grp θ := θ
  rk_sup _ b h := rk_supD h b
  rk_un _ h := h.elim

theorem sysD_sup (θ : Pt × ℕ) (b : Bool) : (sysD Γ).sup θ b = Γ.supD θ b := rfl

theorem selD_good (hΓ : Γ.Good) {θ : Pt × ℕ} (h : Γ.NFv θ ∨ Γ.NFa θ) (c : Option (Fin 4)) :
    (Γ.selD θ ((sysD Γ).good c θ)).1.1 ≠ c := by
  show (Γ.selD θ (decide ((Γ.selD θ true).1.1 ≠ c))).1.1 ≠ c
  by_cases hc : (Γ.selD θ true).1.1 = c
  · rw [decide_eq_false (not_not.mpr hc)]
    intro h'
    exact selD_ne hΓ h (hc.trans h'.symm)
  · rw [decide_eq_true hc]
    exact hc

/-- The potentials of the bookkeeping point: `ψ₀ = 5Σχ`, `ψ_i = -5χ_i`, `χ = P + v(s + j)`. -/
theorem isPotential_psiD (hΓ : Γ.Good) :
    (sysD Γ).IsPotential (fun c θ => psi c θ.1) 85 715 := by
  refine ⟨fun θ => ?_, fun θ c h => ?_, fun θ b c _ => ?_, fun _ _ h => h.elim⟩
  · show ∑ c, psi c θ.1 = 0
    rw [Fintype.sum_option]
    exact UND.Param.psi_sum θ.1.1.2 θ.1.2
  · exact (psi_par c θ.1 _ _).2 (selD_good hΓ h c)
  · exact (psi_par c θ.1 _ _).1

variable (Γ) in
/-- The reached vertices: wrong live virtual values, or marked actual points no later than `s`. -/
def Inv (θ : Pt × ℕ) : Prop :=
  Γ.NFv θ ∨ (θ.2 = 0 ∧ θ.1.2 ≤ Γ.s ∧ marked Γ.E θ.1.2 θ.1.1)

theorem inv_reach (hΓ : Γ.Good) {a b : Pt × ℕ} (h : (sysD Γ).Reach a b) (ha : Inv Γ a) :
    Inv Γ b := by
  induction h with
  | refl => exact ha
  | tail _ hst ih =>
    rcases hst with ⟨hnf, bb, rfl⟩ | ⟨hu, -⟩
    · rename_i x _
      obtain ⟨hc, -⟩ := childOK_sel hΓ hnf bb
      rw [sysD_sup]
      unfold ChildOK at hc
      by_cases h0 : x.2 = 0
      · rw [ite_eq_left h0] at hc
        rcases ih with hv | ⟨-, hs, -⟩
        · exact absurd hv.1 (by omega)
        · refine Or.inr ⟨by show x.2 - 1 = 0; omega, ?_, hc.1⟩
          show (Γ.supD x bb).1.2 ≤ Γ.s
          rw [supD, par_time]
          omega
      · rw [ite_eq_right h0] at hc
        by_cases h1 : x.2 = 1
        · rw [ite_eq_left h1] at hc
          exact Or.inr ⟨by show x.2 - 1 = 0; omega, hc.2, hc.1⟩
        · rw [ite_eq_right h1] at hc
          exact Or.inl hc
    · exact hu.elim

/-- A reached terminal vertex is a flag at level `0`, no later than `s`. -/
theorem flag_of_termD {θ : Pt × ℕ} (hi : Inv Γ θ) (ht : (sysD Γ).IsTerm θ) :
    θ.2 = 0 ∧ θ.1.2 ≤ Γ.s ∧ Γ.E θ.1.2 θ.1.1 := by
  rcases hi with hv | ⟨h0, hs, hm⟩
  · exact absurd (Or.inl hv) ht.1
  · refine ⟨h0, hs, ?_⟩
    by_contra hE
    exact ht.1 (Or.inr ⟨h0, hm, hE⟩)

/-- Along a greedy arm each binary edge lowers the level by at most one. -/
theorem gBin_add_level (c : Option (Fin 4)) (θ : Pt × ℕ) :
    θ.2 ≤ (sysD Γ).gBin c θ + ((sysD Γ).gEnd c θ).2 := by
  refine (sysD Γ).g_induction c (P := fun θ => θ.2 ≤ (sysD Γ).gBin c θ + ((sysD Γ).gEnd c θ).2)
    (fun θ h ih => ?_) (fun θ h => ?_) θ
  · rcases h with h | h
    · rw [(sysD Γ).gBin_of_NF c h, (sysD Γ).gEnd_of_step c (Or.inl h)]
      have e : ((sysD Γ).g c θ).2 = θ.2 - 1 := by
        rw [(sysD Γ).g_of_NF h]
        rfl
      rw [e] at ih
      omega
    · exact h.elim
  · rw [(sysD Γ).gBin_of_isTerm c h, (sysD Γ).gEnd_of_isTerm c h]
    omega

theorem gLen_eq_gBinD (c : Option (Fin 4)) (θ : Pt × ℕ) :
    (sysD Γ).gLen c θ = (sysD Γ).gBin c θ := by
  refine (sysD Γ).g_induction c (P := fun θ => (sysD Γ).gLen c θ = (sysD Γ).gBin c θ)
    (fun θ h ih => ?_) (fun θ h => ?_) θ
  · rcases h with h | h
    · rw [(sysD Γ).gLen_of_step c (Or.inl h), (sysD Γ).gBin_of_NF c h, ih]
    · exact h.elim
  · rw [(sysD Γ).gLen_of_isTerm c h, (sysD Γ).gBin_of_isTerm c h]

/-- Every arm edge is a support step `{θ, supD θ b}` from a binary vertex. -/
theorem armEdge_specD {P : Finset (GroupedSystem.Pole (Pt × ℕ) (Option (Fin 4)))}
    (hP : ∀ σ ∈ P, Γ.NFv σ.loc ∨ Γ.NFa σ.loc) :
    ∀ d ∈ (sysD Γ).armEdges P, ∃ θ b, (Γ.NFv θ ∨ Γ.NFa θ) ∧ d = s(θ, Γ.supD θ b) := by
  intro d hd
  obtain ⟨σ, hσ, hd⟩ := Finset.mem_biUnion.mp hd
  obtain ⟨c, -, hd⟩ := Finset.mem_biUnion.mp hd
  rcases Finset.mem_insert.mp hd with rfl | hd
  · exact ⟨σ.loc, σ.fs c, hP σ hσ, rfl⟩
  · obtain ⟨a, -, hna, rfl⟩ := (sysD Γ).gEdges_spec c _ d hd
    rcases hna with hna | hna
    · exact ⟨a, _, hna, by rw [(sysD Γ).g_of_NF hna]; rfl⟩
    · exact hna.elim

end Ctx

/-! ## The deep contour graph -/

/-- The graph of support steps between levels (both directions; actual steps stay at level `0`). -/
def nbrD (θ : Pt × ℕ) : Finset (Pt × ℕ) :=
  ((box 1 ×ˢ (Finset.univ : Finset Prov)).image (fun p => (par θ.1 p.2 p.1, θ.2 - 1)) ∪
    (box 1 ×ˢ (Finset.univ : Finset Prov)).image (fun p => (par θ.1 p.2 p.1, θ.2))) ∪
  ((box 1 ×ˢ (Finset.univ : Finset Prov)).image (fun p => (chi θ.1 p.2 p.1, θ.2 + 1)) ∪
    (box 1 ×ˢ (Finset.univ : Finset Prov)).image (fun p => (chi θ.1 p.2 p.1, θ.2)))

/-- The deep graph has degree at most `36q`. -/
theorem card_nbrD_le (θ : Pt × ℕ) : (nbrD θ).card ≤ 36 * UND.Param.q := by
  have h : (box 1 ×ˢ (Finset.univ : Finset Prov)).card = 9 * UND.Param.q := by
    rw [Finset.card_product, card_box_one, Finset.card_univ, card_Prov]
  have hi : ∀ f : FNE.Plane × Prov → Pt × ℕ,
      ((box 1 ×ˢ (Finset.univ : Finset Prov)).image f).card ≤ 9 * UND.Param.q :=
    fun f => Finset.card_image_le.trans h.le
  unfold nbrD
  refine (Finset.card_union_le _ _).trans ?_
  have h1 := (Finset.card_union_le
    ((box 1 ×ˢ (Finset.univ : Finset Prov)).image (fun p => (par θ.1 p.2 p.1, θ.2 - 1)))
    ((box 1 ×ˢ (Finset.univ : Finset Prov)).image (fun p => (par θ.1 p.2 p.1, θ.2))))
  have h2 := (Finset.card_union_le
    ((box 1 ×ˢ (Finset.univ : Finset Prov)).image (fun p => (chi θ.1 p.2 p.1, θ.2 + 1)))
    ((box 1 ×ˢ (Finset.univ : Finset Prov)).image (fun p => (chi θ.1 p.2 p.1, θ.2))))
  have := hi (fun p => (par θ.1 p.2 p.1, θ.2 - 1))
  have := hi (fun p => (par θ.1 p.2 p.1, θ.2))
  have := hi (fun p => (chi θ.1 p.2 p.1, θ.2 + 1))
  have := hi (fun p => (chi θ.1 p.2 p.1, θ.2))
  omega

/-- A support step lies in the deep graph, in both directions. -/
theorem inGraphD_step {θ : Pt × ℕ} {π : Prov} {μ : Plane} (hμ : μ ∈ box 1) :
    ∀ a b, s(a, b) = s(θ, (par θ.1 π μ, θ.2 - 1)) → b ∈ nbrD a := by
  have hm : (μ, π) ∈ box 1 ×ˢ (Finset.univ : Finset Prov) :=
    Finset.mem_product.mpr ⟨hμ, Finset.mem_univ _⟩
  intro a b h
  rcases Sym2.eq_iff.mp h with ⟨ha, hb⟩ | ⟨ha, hb⟩
  · rw [ha, hb]
    exact Finset.mem_union_left _ (Finset.mem_union_left _ (Finset.mem_image.mpr ⟨_, hm, rfl⟩))
  · rw [ha, hb]
    by_cases h0 : θ.2 = 0
    · refine Finset.mem_union_right _ (Finset.mem_union_right _
        (Finset.mem_image.mpr ⟨_, hm, ?_⟩))
      exact Prod.ext (chi_par θ.1 π μ) (by show θ.2 - 1 = θ.2; omega)
    · refine Finset.mem_union_right _ (Finset.mem_union_left _
        (Finset.mem_image.mpr ⟨_, hm, ?_⟩))
      exact Prod.ext (chi_par θ.1 π μ) (by show θ.2 - 1 + 1 = θ.2; omega)

theorem not_isDiag_step (θ : Pt × ℕ) (π : Prov) (μ : Plane) (j : ℕ) :
    ¬ (s(θ, (par θ.1 π μ, j))).IsDiag := by
  rw [Sym2.mk_isDiag_iff]
  intro h
  exact par_ne θ.1 π μ (congrArg Prod.fst h).symm

/-! ## Deep contours -/

section DeepContour

open Ctx

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData B τ}

/-- **A deep contour** at a root vertex: `f = |Fl| ≥ 1` distinct raw flags, `e` positive support
edges with `85 e ≤ 4000(f - 1)` and `e ≥` the root level (every arm crosses every virtual level),
flags no later than the queried input time `s` and no earlier than `root time - e`, and at most
`e` edges of the deep graph connected at the root, containing every flag. -/
def IsDeepContour (Γ : Ctx CD) (root : Pt × ℕ) (e : ℕ) (Fl : Finset Pt)
    (K : Finset (Sym2 (Pt × ℕ))) : Prop :=
  1 ≤ Fl.card ∧ 85 * e ≤ 4000 * (Fl.card - 1) ∧ root.2 ≤ e ∧ (∀ y ∈ Fl, Γ.E y.2 y.1) ∧
    (∀ y ∈ Fl, root.1.2 - e ≤ y.2 ∧ y.2 ≤ Γ.s) ∧ ConnectedAt K root ∧ K.card ≤ e ∧
    UND.Counting.InGraph nbrD K ∧ (∀ y ∈ Fl, ∃ d ∈ K, ((y, 0) : Pt × ℕ) ∈ d)

/-- **Lemma 5.4, the contour**: Lemma 5.1 on the deep contour graph of a wrong live virtual
value. -/
theorem exists_deep_contour {Γ : Ctx CD} (hΓ : Γ.Good) {root : Pt × ℕ} (hr : Γ.NFv root) :
    ∃ e Fl K, IsDeepContour Γ root e Fl K := by
  classical
  obtain ⟨P, hroot, hvalid, hlink, hinj, -, hb⟩ :=
    (sysD Γ).grouped_terminal_estimate (Ctx.isPotential_psiD hΓ) (by norm_num)
      ((sysD Γ).hosc_singleton (ψ := fun c θ => psi c θ.1) (fun _ _ _ _ h => h))
      (ρ := root) (Or.inl hr)
  have hC : Fintype.card (Option (Fin 4)) = 5 := by simp
  rw [hC] at hb
  push_cast at hb
  have hPnf : ∀ σ ∈ P, Γ.NFv σ.loc ∨ Γ.NFa σ.loc := fun σ hσ => (hvalid σ hσ).2
  have hreach : ∀ σ ∈ P, ∀ c, (sysD Γ).Reach root ((sysD Γ).pEnd σ c) := fun σ hσ c =>
    ((hvalid σ hσ).1.trans ((sysD Γ).reach_sup (hvalid σ hσ).2 _)).trans
      ((sysD Γ).reach_gEnd c _)
  have hend : ∀ σ ∈ P, ∀ c, ((sysD Γ).pEnd σ c).2 = 0 ∧ ((sysD Γ).pEnd σ c).1.2 ≤ Γ.s ∧
      Γ.E ((sysD Γ).pEnd σ c).1.2 ((sysD Γ).pEnd σ c).1.1 := fun σ hσ c =>
    Ctx.flag_of_termD (Ctx.inv_reach hΓ (hreach σ hσ c) (Or.inl hr)) ((sysD Γ).pEnd_isTerm σ c)
  have hspan := (sysD Γ).witness_span (fun θ => θ.1.2)
    (fun θ b _ => by show θ.1.2 - 1 + 1 = θ.1.2; ring) (fun θ h => h.elim)
    (fun φ φ' _ _ h => congrArg (fun θ : Pt × ℕ => θ.1.2) h) hvalid hlink
  have hKarm : ((sysD Γ).witness P).filter (fun d => ¬ d.IsDiag) ⊆ (sysD Γ).armEdges P := by
    intro d hd
    obtain ⟨hdw, hnd⟩ := Finset.mem_filter.mp hd
    rcases Finset.mem_union.mp hdw with h | h
    · exact h
    · exfalso
      obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp h
      have heq : (sysD Γ).pEnd p.1.1 p.1.2 = (sysD Γ).pEnd p.2.1 p.2.2 :=
        ((@Finset.mem_filter _ _ (fun _ => Classical.propDecidable _) _ _).mp hp).2
      exact hnd (by rw [heq]; exact Sym2.mk_isDiag_iff.mpr rfl)
  have harm := Ctx.armEdge_specD hPnf
  have hendK : ∀ σ ∈ P, ∀ c, ∃ d ∈ ((sysD Γ).witness P).filter (fun d => ¬ d.IsDiag),
      (sysD Γ).pEnd σ c ∈ d := by
    intro σ hσ c
    have hr' := ((sysD Γ).pEdges_reach σ c).2
    have hne : σ.loc ≠ (sysD Γ).pEnd σ c := by
      intro h
      have h1 := (sysD Γ).time_le_of_reach (fun θ => θ.1.2)
        (fun θ b _ => by show θ.1.2 - 1 + 1 = θ.1.2; ring) (fun θ h => h.elim)
        ((sysD Γ).reach_gEnd c ((sysD Γ).pFirst σ c))
      have h2 : ((sysD Γ).pFirst σ c).1.2 = σ.loc.1.2 - 1 := rfl
      have h3 : ((sysD Γ).pEnd σ c).1.2 = σ.loc.1.2 := by rw [← h]
      unfold GroupedSystem.pEnd at h3
      omega
    obtain ⟨d, hd, hmem⟩ := exists_edge_of_reach hr' hne
    have hdw := (sysD Γ).pEdges_subset_witness hσ c hd
    have hda : d ∈ (sysD Γ).armEdges P :=
      Finset.mem_biUnion.mpr ⟨σ, hσ, Finset.mem_biUnion.mpr ⟨c, Finset.mem_univ _, hd⟩⟩
    obtain ⟨y, b, hy, rfl⟩ := harm d hda
    exact ⟨_, Finset.mem_filter.mpr ⟨hdw, not_isDiag_step _ _ _ _⟩, hmem⟩
  have hlen : ∀ σ c, (sysD Γ).pLen σ c = (sysD Γ).pBin σ c := fun σ c => by
    unfold GroupedSystem.pLen GroupedSystem.pBin
    rw [Ctx.gLen_eq_gBinD]
  have hinjE : Set.InjOn (fun σ => ((sysD Γ).pEnd σ none).1)
      (P : Set (GroupedSystem.Pole (Pt × ℕ) (Option (Fin 4)))) := by
    intro σ hσ σ' hσ' h
    refine hinj none σ hσ σ' hσ' (Prod.ext h ?_)
    show ((sysD Γ).pEnd σ none).2 = ((sysD Γ).pEnd σ' none).2
    rw [(hend σ hσ none).1, (hend σ' hσ' none).1]
  have hcard : (P.image (fun σ => ((sysD Γ).pEnd σ none).1)).card = P.card :=
    Finset.card_image_of_injOn hinjE
  have hP1 : 1 ≤ P.card := Finset.card_pos.mpr ⟨_, hroot⟩
  -- every root arm crosses every level
  have hrootbin : root.2 ≤ (sysD Γ).pBin ((sysD Γ).rootPole root) none := by
    have h1 := Ctx.gBin_add_level (Γ := Γ) none ((sysD Γ).pFirst ((sysD Γ).rootPole root) none)
    have h2 := (hend _ hroot none).1
    unfold GroupedSystem.pEnd at h2
    rw [h2] at h1
    have h3 : ((sysD Γ).pFirst ((sysD Γ).rootPole root) none).2 = root.2 - 1 := rfl
    unfold GroupedSystem.pBin
    omega
  have hege : (sysD Γ).pBin ((sysD Γ).rootPole root) none ≤
      ∑ σ ∈ P, ∑ c, (sysD Γ).pBin σ c :=
    (Finset.single_le_sum (f := fun c => (sysD Γ).pBin ((sysD Γ).rootPole root) c)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ none)).trans
      (Finset.single_le_sum (f := fun σ => ∑ c, (sysD Γ).pBin σ c)
        (fun _ _ => Nat.zero_le _) hroot)
  refine ⟨∑ σ ∈ P, ∑ c, (sysD Γ).pBin σ c, P.image (fun σ => ((sysD Γ).pEnd σ none).1),
    ((sysD Γ).witness P).filter (fun d => ¬ d.IsDiag), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hcard]; exact hP1
  · rw [hcard]
    have : ((∑ σ ∈ P, ∑ c, (sysD Γ).pBin σ c : ℕ) : ℤ) =
        ∑ σ ∈ P, ∑ c, ((sysD Γ).pBin σ c : ℤ) := by push_cast; rfl
    have hb' : (85 : ℤ) * ((∑ σ ∈ P, ∑ c, (sysD Γ).pBin σ c : ℕ) : ℤ) ≤
        4000 * ((P.card : ℤ) - 1) := by rw [this]; linarith
    omega
  · omega
  · intro y hy
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hy
    exact (hend σ hσ none).2.2
  · intro y hy
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨d, hd, hmem⟩ := hendK σ hσ none
    have := hspan d (Finset.mem_filter.mp hd).1 _ hmem
    refine ⟨?_, (hend σ hσ none).2.1⟩
    push_cast
    linarith [this.2]
  · exact UND.Counting.connectedAt_filter_not_diag ((sysD Γ).witness_connected hlink)
  · refine (Finset.card_le_card hKarm).trans (((sysD Γ).armEdges_card_le P).trans ?_)
    exact le_of_eq (Finset.sum_congr rfl fun σ _ => Finset.sum_congr rfl fun c _ => hlen σ c)
  · intro a b hab
    obtain ⟨y, bb, hy, he⟩ := harm _ (hKarm hab)
    exact inGraphD_step (Ctx.childOK_sel hΓ hy bb).2 a b he
  · intro y hy
    obtain ⟨σ, hσ, rfl⟩ := Finset.mem_image.mp hy
    obtain ⟨d, hd, hmem⟩ := hendK σ hσ none
    refine ⟨d, hd, ?_⟩
    have e : (((sysD Γ).pEnd σ none).1, 0) = (sysD Γ).pEnd σ none :=
      Prod.ext rfl (hend σ hσ none).1.symm
    rw [e]
    exact hmem

end DeepContour

/-! ## Lemma 5.4 -/

section Lemma

open Ctx

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData B τ}

/-- The root of the deep query `Q_t(w)`: virtual level `T` at `w - (T - 1)v`, bookkeeping time
`t - 1 + T` (its characteristic coordinate `P - (T-1)v + v(t - 1 + T) = P + vt` is the current
one: "recentring in (3) places the query root at the current characteristic coordinate"). -/
def qRoot (t : ℤ) (w : ISite) : Pt × ℕ := ((w - qShift, t - 1 + UND.Param.T), UND.Param.T)

/-- The context of a deep query at proposal time `t`: data `D_{t-1}`. -/
def ctxOf (X : ℤ → PConfig CD) (E : ℤ → ISite → Prop) (c : Plane → LiveLetter CD.toWangRel)
    (t : ℤ) : Ctx CD :=
  ⟨E, dataOf (X (t - 1)), c, t - 1⟩

/-- **Lemma 5.4** (deep wrong readings). Relative to a chart `c` agreeing with every unmarked live
reading (Lemma 5.3, `coherent_chart`), a wrong live deep query `Q_t(w) = a ≠ c(u)` has a finite
contour with `f ≥ 11` distinct raw flags and `e ≤ 50(f - 1)` support edges (`T ≤ e`: every arm
crosses all `T` virtual levels); all its flags are no later than the queried input time `t - 1`,
and its earliest flag time `t₀` satisfies `t - t₀ ≤ e`; the contour is a set of at most `e` edges
of the deep graph connected at the query root and containing every flag. -/
theorem deep_wrong {X : ℤ → PConfig CD} {E : ℤ → ISite → Prop}
    {c : Plane → LiveLetter CD.toWangRel}
    (hc : ∀ t u P a, UL CD X (marked E) t (u, P) a → c u = a) {t : ℤ} {w : ISite}
    {a : LiveLetter CD.toWangRel} (hq : drvQ (X (t - 1)) w = some a) (ha : a ≠ c w.1) :
    ∃ (e : ℕ) (Fl : Finset Pt) (K : Finset (Sym2 (Pt × ℕ))),
      11 ≤ Fl.card ∧ e ≤ 50 * (Fl.card - 1) ∧ UND.Param.T ≤ e ∧
      (∀ y ∈ Fl, E y.2 y.1) ∧ (∀ y ∈ Fl, t - e ≤ y.2 ∧ y.2 ≤ t - 1) ∧
      ConnectedAt K (qRoot t w) ∧ K.card ≤ e ∧ UND.Counting.InGraph nbrD K ∧
      (∀ y ∈ Fl, ∃ d ∈ K, ((y, 0) : Pt × ℕ) ∈ d) := by
  have hΓ : (ctxOf X E c t).Good := by
    intro w' a' hw' hne
    by_contra hm
    exact hne (hc (t - 1) w'.1 w'.2 a' ⟨hm, Or.inl hw'⟩).symm
  have hr : (ctxOf X E c t).NFv (qRoot t w) := by
    refine ⟨by show 1 ≤ UND.Param.T; rw [T_eq]; norm_num, rfl, a, hq, ?_⟩
    show a ≠ c (w - qShift).1
    simpa [qShift] using ha
  obtain ⟨e, Fl, K, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩ := exists_deep_contour hΓ hr
  have hT : UND.Param.T ≤ e := h3
  have hT' := hT
  rw [T_eq] at hT'
  refine ⟨e, Fl, K, ?_, ?_, hT, h4, ?_, h6, h7, h8, h9⟩
  · omega
  · omega
  · intro y hy
    obtain ⟨a1, a2⟩ := h5 y hy
    have e1 : (qRoot t w).1.2 = t - 1 + UND.Param.T := rfl
    rw [e1, T_eq] at a1
    exact ⟨by omega, a2⟩

/-- **Lemma 5.4, at lag `ℓ ≤ W`**: for the query at lag `ℓ` from the current output time `t + ℓ`,
the earliest flag time `t₀` satisfies `(t + ℓ) - t₀ ≤ W + 50(f - 1)`. -/
theorem deep_wrong_lag {X : ℤ → PConfig CD} {E : ℤ → ISite → Prop}
    {c : Plane → LiveLetter CD.toWangRel}
    (hc : ∀ t u P a, UL CD X (marked E) t (u, P) a → c u = a) {t : ℤ} {w : ISite}
    {a : LiveLetter CD.toWangRel} (hq : drvQ (X (t - 1)) w = some a) (ha : a ≠ c w.1)
    {ℓ W : ℕ} (hℓ : ℓ ≤ W) :
    ∃ (e : ℕ) (Fl : Finset Pt) (K : Finset (Sym2 (Pt × ℕ))),
      11 ≤ Fl.card ∧ e ≤ 50 * (Fl.card - 1) ∧ (∀ y ∈ Fl, E y.2 y.1) ∧
      (∀ y ∈ Fl, y.2 ≤ t - 1 ∧ t + ℓ - y.2 ≤ W + ((50 * (Fl.card - 1) : ℕ) : ℤ)) ∧
      ConnectedAt K (qRoot t w) ∧ K.card ≤ e ∧ UND.Counting.InGraph nbrD K ∧
      (∀ y ∈ Fl, ∃ d ∈ K, ((y, 0) : Pt × ℕ) ∈ d) := by
  obtain ⟨e, Fl, K, h1, h2, -, h4, h5, h6, h7, h8, h9⟩ := deep_wrong hc hq ha
  refine ⟨e, Fl, K, h1, h2, h4, fun y hy => ?_, h6, h7, h8, h9⟩
  obtain ⟨a1, a2⟩ := h5 y hy
  exact ⟨a2, by omega⟩

end Lemma

end UND.Deep
