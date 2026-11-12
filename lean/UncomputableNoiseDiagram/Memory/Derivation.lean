/-
# Lemma 7.1 (error decomposition) as a grouped derivation (Mem2, Mem3 instance)

Node Mem2 (the derivation) and the instance part of Mem3 of `BLUEPRINT.md` (Part A.7), NEW (on
Lemma 5.1, `Contour/Grouped.lean`; the memory encodings of Lemma 7.2, `Memory/Count.lean`; the
helper ride, `Memory/Ride.lean`).

Paper (Section 7): "Call a data value or driver bad when it differs from the reference live
letter, including when it is bottom. If an ordinary forecast is bad, at least `q - h + 1 = K + 1`
checked providers fail to give the correct letter. Each such check has a bad Moore input. They
occupy at least two clusters. Thus a bad forecast admits a two-cluster bad support. The same
assertion holds at each virtual iteration of a bad deep driver."
Lemma 7.1: "Every finite-time data or second-coordinate error has a finite acyclic derivation whose
terminal sources are raw or statistical bins, whose branching steps are ordinary or virtual
two-cluster supports, and whose remaining links follow one base characteristic for a lag at most
`W`. Each such characteristic link is followed by a positive support step before another
source-free link is needed."
Lemma 7.2 (proof): "For an actual `D_s(u,P)` assign characteristic provider coordinate `P + vs`,
planar coordinate `(u_x - s, u_y)` and bin `⌊s/W⌋`. For virtual `F_R^j(D_s)(u,P)` use
`P + vs + jv`, planar coordinate `(u_x - s - 1, u_y)`, that bin and its level `j`. A recentered `Q`
root has exactly its output's characteristic coordinates. … Project the selected witness to
characteristic coordinates, bin, virtual level and finite role …"

Formalization (deterministic, for one trajectory `Y`, one noise `ω`, a reference full chart):
* vertices `(y, j) : Pt × ℕ` as in Lemma 5.4: `j = 0` the data `D_t(w)` (`y = (w, t)`), `j ≥ 1`
  the virtual value `F_R^j(D_{t-j})(w)` at the bookkeeping time `t` (`val`); `aV y` (the ordinary
  driver `A_t(w)`, level `1`), `qV y` (the deep driver `Q_t(w)`, level `T`), `rideBase y i` (the
  `i`-th earlier base on the base characteristic); **bad** = `≠` the reference letter (`Bad`);
* binary vertices: bad virtual values (`NFv`) and bad unflagged data with a bad ordinary driver
  (`NFd`), with two bad supports in distinct clusters (`exists_pgood`: more than `K` failed checks,
  each with a bad Moore input); unary vertices (`UNd`): bad unflagged data with a correct ordinary
  driver and a bad driver node (`Link`) at the output's deep driver or on the ride (lag `≤ W`),
  always a binary vertex, so no unary link follows another; the rank `rkM` (`(T+1)·(t - j) + j`);
  **`sysM`** (a `GroupedSystem`), **`isPotential_sysM`** (the characteristic potentials,
  `psi_eq_chi`: `ψ` depends only on `χ = P + vt`);
* the projection `fM` to (characteristic, bin, level) and the graph `nbrM` of degree `≤ 108q + 6`
  (`card_nbrM_le`); the groups are the projections themselves (`grp = fM`), so terminal leaves of
  one group project to one point;
* `Hyp` (the trajectory follows the rule off flags at positive times, the data are the chart at
  times `≤ 0`, the helpers follow (4) at all times, and the chart's gates: depth, row flag, origin
  `ℓ_d` sites back); **`term_source`** (Lemma 7.1: a reached terminal leaf is a flagged output, a
  raw source, or an erasure at a correct gate whose intrinsic bad event holds, a statistical
  source: `hcount_short`, `lcount_long`);
* **`mem_cover`** (Lemmas 7.1 and 7.2): a data error at `(w, t)` has a literal encoding at the
  projected root with `g ≥ 1` labels, at most `256g` edges, every label a raw or statistical
  source.
-/
import UncomputableNoiseDiagram.Memory.Count
import UncomputableNoiseDiagram.Memory.Ride
import UncomputableNoiseDiagram.Contour.Deep
import UncomputableNoiseDiagram.Sensors.Joint

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option synthInstance.maxSize 512

noncomputable section

open Relation

namespace UND.Memory

open UND.Rule UND.Sensors UND.Raw UND.Contour
open UPD.Scaffold (IsLeftEnd IsRightEnd phaseOffsets)
open FNE (Plane box)

/- D21: `T` stays opaque. -/
attribute [local irreducible] UND.Param.T

theorem one_le_T : 1 ≤ UND.Param.T := by rw [UND.Deep.T_eq]; norm_num

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] {CD : ChartData B τ}

/-! ## Vertices -/

/-- The value of a vertex `(y, j)`: the data `D_t(w)` at level `0` (`y = (w, t)`), the virtual
value `F_R^j(D_{t-j})(w)` at level `j ≥ 1` (bookkeeping time `t`). -/
def val (Y : ℤ → PConfig CD) (θ : Pt × ℕ) : ChartSym CD.toWangRel :=
  (FR CD.toWangRel)^[θ.2] (dataOf (Y (θ.1.2 - θ.2))) θ.1.1

/-- The ordinary driver vertex `A_t(w) = F_R(D_{t-1})(w)` of `y = (w, t)` (level `1`). -/
def aV (y : Pt) : Pt × ℕ := (y, 1)

/-- The deep driver vertex `Q_t(w) = F_R^T(D_{t-1})(w - (T-1)v)` of `y = (w, t)` (level `T`,
bookkeeping time `t - 1 + T`). -/
def qV (y : Pt) : Pt × ℕ := ((y.1 - qShift, y.2 - 1 + (UND.Param.T : ℤ)), UND.Param.T)

/-- The base `i + 1` updates before `y = (w, t)` on its base characteristic. -/
def rideBase (y : Pt) (i : ℕ) : Pt :=
  (((y.1.1.1 - ((i : ℤ) + 1), y.1.1.2), y.1.2 + ((i : ℤ) + 1) • vP), y.2 - 1 - i)

/-- The characteristic provider coordinate `χ = P + vt` of a point. -/
def chiOf (y : Pt) : Fin 4 → ℤ := y.1.2 + y.2 • vP

/-- The output time of a vertex: `t` at level `0`, `t - j + 1` at level `j ≥ 1`. -/
def outT (θ : Pt × ℕ) : ℤ := θ.1.2 - θ.2 + (if θ.2 = 0 then 0 else 1)

theorem val_aV (Y : ℤ → PConfig CD) (y : Pt) : val Y (aV y) = drvA (Y (y.2 - 1)) y.1 := by
  simp [val, aV, drvA]

theorem qV_planar (y : Pt) : (qV y).1.1.1 = y.1.1 := by
  simp [qV, qShift]

theorem val_qV (Y : ℤ → PConfig CD) (y : Pt) : val Y (qV y) = drvQ (Y (y.2 - 1)) y.1 := by
  unfold val qV drvQ
  have e : y.2 - 1 + (UND.Param.T : ℤ) - (UND.Param.T : ℤ) = y.2 - 1 := by ring
  simp only [e]

theorem rideBase_eq (w : ISite) (t : ℤ) (i : ℕ) :
    rideBase (w, t) i = (chSite (w.1.1 - t) w.1.2 (w.2 + t • vP) (t - 1 - i), t - 1 - i) := by
  refine Prod.ext (Prod.ext (Prod.ext ?_ rfl) (funext fun j => ?_)) rfl
  · simp only [rideBase, chSite]
    ring
  · simp only [rideBase, chSite, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, vP, smul_eq_mul]
    ring

theorem chSite_self (w : ISite) (t : ℤ) : chSite (w.1.1 - t) w.1.2 (w.2 + t • vP) t = w := by
  refine Prod.ext (Prod.ext ?_ rfl) ?_
  · simp [chSite]
  · simp [chSite]

theorem chiOf_qV (y : Pt) : chiOf (qV y).1 = chiOf y := by
  funext i
  simp only [chiOf, qV, qShift, qOff, vP, Pi.add_apply, Prod.snd_sub, Pi.sub_apply,
    Pi.smul_apply, smul_eq_mul]
  ring

theorem chiOf_rideBase (y : Pt) (i : ℕ) : chiOf (rideBase y i) = chiOf y := by
  funext j
  simp only [chiOf, rideBase, vP, Pi.add_apply, Pi.smul_apply, smul_eq_mul]
  ring

theorem chiOf_par (y : Pt) (π : Prov) (μ : Plane) :
    chiOf (par y π μ) = chiOf y + provOff π - vP := by
  funext j
  simp only [chiOf, Raw.par, vP, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  ring

/-- The projection to (characteristic coordinates, bin) and level: planar `(u_x - t_out, u_y)`,
provider `χ = P + vt` (bookkeeping time), bin `⌊t_out / W⌋`. -/
def fM (W : ℕ) (θ : Pt × ℕ) : Label × ℕ :=
  (((θ.1.1.1.1 - outT θ, θ.1.1.1.2, chiOf θ.1), outT θ / (W : ℤ)), θ.2)

/-- The potentials are functions of `χ = P + vt`: `ψ₀ = 5Σχ`, `ψ_i = -5χ_i`. -/
def psiChi : Option (Fin 4) → (Fin 4 → ℤ) → ℤ
  | none, χ => 5 * ∑ i, χ i
  | some i, χ => -5 * χ i

theorem psi_eq_chi (c : Option (Fin 4)) (y : Pt) : psi c y = psiChi c (chiOf y) := by
  cases c with
  | none =>
    simp only [psi, psiChi, chiOf, UND.Param.psi0, Pi.add_apply, Pi.smul_apply, vP, smul_eq_mul,
      Finset.sum_add_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  | some i =>
    simp only [psi, psiChi, chiOf, UND.Param.psiI, Pi.add_apply, Pi.smul_apply, vP, smul_eq_mul]
    ring

/-- The support through provider `π` at planar displacement `μ`, one level down. -/
def supOf (θ : Pt × ℕ) (p : Prov × Plane) : Pt × ℕ := (par θ.1 p.1 p.2, θ.2 - 1)

theorem supOf_aV {θ : Pt × ℕ} (h0 : θ.2 = 0) (p : Prov × Plane) :
    supOf (aV θ.1) p = supOf θ p := by
  simp [supOf, aV, h0]

/-! ## The derivation -/

/-- The data of Lemma 7.1: a trajectory `Y`, a noise `ω`, a reference chart and the bin width. -/
structure MCtx (CD : ChartData B τ) where
  /-- the trajectory (data, second coordinate, helpers) at every integer time -/
  Y : ℤ → PConfig CD
  /-- the two-sided noise -/
  ω : PNoise CD
  /-- the reference chart -/
  ref : Plane → LiveLetter CD.toWangRel
  /-- the bin width `W` -/
  W : ℕ

namespace MCtx

variable (Γ : MCtx CD)

/-- A bad value: different from the reference letter (including `⊥`). -/
def Bad (θ : Pt × ℕ) : Prop := val Γ.Y θ ≠ some (Γ.ref θ.1.1.1)

/-- The output of a level-`0` vertex is flagged. -/
def Fl (θ : Pt × ℕ) : Prop := flagAt Γ.ω θ.1.2 θ.1.1 = true

/-- A characteristic link from a data vertex: a bad driver node at its deep driver, or at a ride
base at lag `≤ W` on its base characteristic. -/
def Link (θ η : Pt × ℕ) : Prop :=
  1 ≤ η.2 ∧ Γ.Bad η ∧
    (η = qV θ.1 ∨ ∃ i < Γ.W, η = aV (rideBase θ.1 i) ∨ η = qV (rideBase θ.1 i))

/-- Binary virtual vertices: bad virtual values. -/
def NFv (θ : Pt × ℕ) : Prop := 1 ≤ θ.2 ∧ Γ.Bad θ

/-- Binary data vertices: bad unflagged data with a bad ordinary driver. -/
def NFd (θ : Pt × ℕ) : Prop :=
  θ.2 = 0 ∧ 1 ≤ θ.1.2 ∧ Γ.Bad θ ∧ ¬ Γ.Fl θ ∧ Γ.Bad (aV θ.1)

/-- Unary vertices: bad unflagged data with a correct ordinary driver and a characteristic link. -/
def UNd (θ : Pt × ℕ) : Prop :=
  θ.2 = 0 ∧ 1 ≤ θ.1.2 ∧ Γ.Bad θ ∧ ¬ Γ.Fl θ ∧ ¬ Γ.Bad (aV θ.1) ∧ ∃ η, Γ.Link θ η

/-- An admissible choice of two bad supports in distinct clusters. -/
def PGood (θ : Pt × ℕ) (d : (Prov × Plane) × (Prov × Plane)) : Prop :=
  d.1.1.1 ≠ d.2.1.1 ∧ d.1.2 ∈ box 1 ∧ d.2.2 ∈ box 1 ∧ Γ.Bad (supOf θ d.1) ∧
    Γ.Bad (supOf θ d.2)

/-- The chosen supports. -/
def pd (θ : Pt × ℕ) : (Prov × Plane) × (Prov × Plane) := Classical.epsilon (Γ.PGood θ)

/-- The selected support `b`. -/
def sel (θ : Pt × ℕ) (b : Bool) : Prov × Plane := if b then (Γ.pd θ).1 else (Γ.pd θ).2

/-- The chosen link target. -/
def unM (θ : Pt × ℕ) : Pt × ℕ := Classical.epsilon (Γ.Link θ)

variable {Γ}

/-- **A bad value at level `j ≥ 1` has two bad supports in distinct clusters**: more than `K`
checked providers fail, each failed check has a bad Moore input. -/
theorem exists_pgood (hfull : IsFullChart CD.toWangRel Γ.ref) {θ : Pt × ℕ} (hj : 1 ≤ θ.2)
    (hb : Γ.Bad θ) : ∃ d, Γ.PGood θ d := by
  classical
  obtain ⟨⟨⟨u, P⟩, t⟩, j⟩ := θ
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by simp only at hj; omega⟩
  set D' := (FR CD.toWangRel)^[i] (dataOf (Γ.Y (t - ((i + 1 : ℕ) : ℤ)))) with hD'
  have hval : val Γ.Y (((u, P), t), i + 1) = FR CD.toWangRel D' (u, P) := by
    show (FR CD.toWangRel)^[i + 1] _ _ = _
    rw [Function.iterate_succ_apply']
  have hb' : FR CD.toWangRel D' (u, P) ≠ some (Γ.ref u) := by
    have := hb
    unfold Bad at this
    rwa [hval] at this
  have hlt : quorumCount CD.toWangRel D' (u, P) (Γ.ref u) < UND.Param.h := by
    by_contra hge
    exact hb' ((FR_eq_some_iff CD.toWangRel D' (u, P) (Γ.ref u)).2 (by omega))
  set F := Finset.univ.filter (fun π : Prov =>
    ¬ chk CD.toWangRel (fun v => D' (v, P + provOff π)) u = some (Γ.ref u)) with hF
  have hsum : quorumCount CD.toWangRel D' (u, P) (Γ.ref u) + F.card = UND.Param.q := by
    have := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset Prov))
      (fun π : Prov => chk CD.toWangRel (fun v => D' (v, P + provOff π)) u = some (Γ.ref u))
    rw [Finset.card_univ, card_Prov] at this
    exact this
  have hcard : UND.Param.K < F.card := by
    have hqh : UND.Param.q = UND.Param.h + UND.Param.K := by
      simp only [UND.Param.q, UND.Param.h]; ring
    omega
  obtain ⟨π, hπ, π', hπ', hne⟩ := UND.Deep.exists_two_clusters F hcard
  have key : ∀ π ∈ F, ∃ μ ∈ box 1, D' (u + μ, P + provOff π) ≠ some (Γ.ref (u + μ)) := by
    intro π hπ
    have hf := (Finset.mem_filter.1 hπ).2
    by_contra hall
    push Not at hall
    apply hf
    rw [chk_congr CD.toWangRel (x := fun v => D' (v, P + provOff π))
      (y := fun v => some (Γ.ref v)) (fun d hd => hall d hd)]
    exact chk_chart CD.toWangRel hfull u
  obtain ⟨μ, hμ, h1⟩ := key π hπ
  obtain ⟨μ', hμ', h2⟩ := key π' hπ'
  have hsup : ∀ (π : Prov) (μ : Plane), D' (u + μ, P + provOff π) ≠ some (Γ.ref (u + μ)) →
      Γ.Bad (supOf (((u, P), t), i + 1) (π, μ)) := by
    intro π μ h
    unfold Bad supOf val
    simp only [Raw.par, Nat.add_sub_cancel]
    have e : t - 1 - (i : ℤ) = t - ((i + 1 : ℕ) : ℤ) := by push_cast; ring
    rw [e]
    exact h
  exact ⟨((π, μ), (π', μ')), hne, hμ, hμ', hsup π μ h1, hsup π' μ' h2⟩

theorem exists_pgood_of_NF (hfull : IsFullChart CD.toWangRel Γ.ref) {θ : Pt × ℕ}
    (h : Γ.NFv θ ∨ Γ.NFd θ) : ∃ d, Γ.PGood θ d := by
  rcases h with ⟨hj, hb⟩ | ⟨h0, -, -, -, hb⟩
  · exact exists_pgood hfull hj hb
  · obtain ⟨d, hd⟩ := exists_pgood (Γ := Γ) hfull (θ := aV θ.1) le_rfl hb
    refine ⟨d, ?_⟩
    unfold PGood at hd ⊢
    rwa [supOf_aV h0, supOf_aV h0] at hd

theorem pd_spec (hfull : IsFullChart CD.toWangRel Γ.ref) {θ : Pt × ℕ}
    (h : Γ.NFv θ ∨ Γ.NFd θ) : Γ.PGood θ (Γ.pd θ) :=
  Classical.epsilon_spec (exists_pgood_of_NF hfull h)

theorem sel_spec (hfull : IsFullChart CD.toWangRel Γ.ref) {θ : Pt × ℕ}
    (h : Γ.NFv θ ∨ Γ.NFd θ) (b : Bool) :
    (Γ.sel θ b).2 ∈ box 1 ∧ Γ.Bad (supOf θ (Γ.sel θ b)) := by
  have := pd_spec hfull h
  cases b
  · exact ⟨this.2.2.1, this.2.2.2.2⟩
  · exact ⟨this.2.1, this.2.2.2.1⟩

theorem sel_ne (hfull : IsFullChart CD.toWangRel Γ.ref) {θ : Pt × ℕ}
    (h : Γ.NFv θ ∨ Γ.NFd θ) : (Γ.sel θ true).1.1 ≠ (Γ.sel θ false).1.1 :=
  (pd_spec hfull h).1

theorem unM_spec {θ : Pt × ℕ} (h : Γ.UNd θ) : Γ.Link θ (Γ.unM θ) :=
  Classical.epsilon_spec h.2.2.2.2.2

/-! ### The rank -/

/-- The rank `(T + 1)·(t - j) + j`. -/
def rkM (θ : Pt × ℕ) : ℕ := (UND.Param.T + 1) * (θ.1.2 - θ.2).toNat + θ.2

theorem rk_lt_of {a b j : ℕ} (hab : a + 1 ≤ b) (hj : j ≤ UND.Param.T) :
    (UND.Param.T + 1) * a + j < (UND.Param.T + 1) * b := by
  have : (UND.Param.T + 1) * (a + 1) ≤ (UND.Param.T + 1) * b := Nat.mul_le_mul_left _ hab
  rw [Nat.mul_add, Nat.mul_one] at this
  omega

theorem rk_sup {θ : Pt × ℕ} (h : Γ.NFv θ ∨ Γ.NFd θ) (p : Prov × Plane) :
    rkM (supOf θ p) < rkM θ := by
  unfold rkM supOf
  simp only [par_time]
  rcases h with ⟨hj, -⟩ | ⟨h0, ht, -⟩
  · have e : θ.1.2 - 1 - ((θ.2 - 1 : ℕ) : ℤ) = θ.1.2 - θ.2 := by
      rw [Nat.cast_sub hj]; push_cast; ring
    rw [e]
    omega
  · rw [h0]
    simp only [Nat.zero_sub, Nat.cast_zero, sub_zero, add_zero]
    have := rk_lt_of (a := (θ.1.2 - 1).toNat) (b := θ.1.2.toNat) (j := 0) (by omega)
      (Nat.zero_le _)
    simpa using this

theorem rk_un {θ : Pt × ℕ} (h : Γ.UNd θ) : rkM (Γ.unM θ) < rkM θ := by
  have hL := unM_spec h
  obtain ⟨h0, ht, -⟩ := h
  obtain ⟨-, -, hη⟩ := hL
  unfold rkM
  rw [h0]
  simp only [Nat.cast_zero, sub_zero, add_zero]
  rcases hη with he | ⟨i, -, he | he⟩ <;> rw [he]
  · simp only [qV]
    have e : θ.1.2 - 1 + (UND.Param.T : ℤ) - (UND.Param.T : ℤ) = θ.1.2 - 1 := by ring
    rw [e]
    refine rk_lt_of ?_ le_rfl
    omega
  · simp only [aV, rideBase]
    refine rk_lt_of ?_ one_le_T
    omega
  · simp only [qV, rideBase]
    have e : θ.1.2 - 1 - (i : ℤ) - 1 + (UND.Param.T : ℤ) - (UND.Param.T : ℤ) =
        θ.1.2 - 2 - i := by ring
    rw [e]
    refine rk_lt_of ?_ le_rfl
    omega

/-! ### The system -/

variable (Γ) in
/-- **The derivation of Lemma 7.1** as a grouped system: binary vertices `NFv`, `NFd` with two
bad supports in distinct clusters (charge `c` good: a cluster `≠ c`), unary characteristic links
`UNd`; the groups are the projections `fM`. -/
def sysM : GroupedSystem (Pt × ℕ) (Option (Fin 4)) (Label × ℕ) where
  rk := rkM
  NF θ := Γ.NFv θ ∨ Γ.NFd θ
  UN θ := Γ.UNd θ
  not_UN_of_NF θ h hu := by
    rcases h with ⟨hj, -⟩ | ⟨-, -, -, -, hb⟩
    · rw [hu.1] at hj; exact absurd hj (by norm_num)
    · exact hu.2.2.2.2.1 hb
  sup θ b := supOf θ (Γ.sel θ b)
  un := Γ.unM
  good c θ := decide ((Γ.sel θ true).1.1 ≠ c)
  grp := fM Γ.W
  rk_sup θ b h := rk_sup h _
  rk_un θ h := rk_un h

theorem sel_good (hfull : IsFullChart CD.toWangRel Γ.ref) {θ : Pt × ℕ}
    (h : Γ.NFv θ ∨ Γ.NFd θ) (c : Option (Fin 4)) :
    (Γ.sel θ ((sysM Γ).good c θ)).1.1 ≠ c := by
  show (Γ.sel θ (decide ((Γ.sel θ true).1.1 ≠ c))).1.1 ≠ c
  by_cases hc : (Γ.sel θ true).1.1 = c
  · rw [decide_eq_false (not_not.mpr hc)]
    intro h'
    exact sel_ne hfull h (hc.trans h'.symm)
  · rw [decide_eq_true hc]
    exact hc

/-- **The characteristic potentials** `ψ₀ = 5Σχ`, `ψ_i = -5χ_i` (gains `85`, worst `-715`;
characteristic links keep `χ`). -/
theorem isPotential_sysM (hfull : IsFullChart CD.toWangRel Γ.ref) :
    (sysM Γ).IsPotential (fun c θ => psi c θ.1) 85 715 := by
  refine ⟨fun θ => ?_, fun θ c h => ?_, fun θ b c _ => ?_, fun θ c h => ?_⟩
  · show ∑ c, psi c θ.1 = 0
    rw [Fintype.sum_option]
    exact UND.Param.psi_sum θ.1.1.2 θ.1.2
  · exact (psi_par c θ.1 _ _).2 (sel_good hfull h c)
  · exact (psi_par c θ.1 _ _).1
  · show psi c (Γ.unM θ).1 = psi c θ.1
    obtain ⟨-, -, hη⟩ := unM_spec h
    rw [psi_eq_chi, psi_eq_chi]
    congr 1
    rcases hη with he | ⟨i, -, he | he⟩ <;> rw [he]
    · exact chiOf_qV _
    · exact chiOf_rideBase _ _
    · rw [chiOf_qV, chiOf_rideBase]

/-- Leaves of one group have equal potentials (they share `χ`). -/
theorem hgrp_sysM (φ φ' : Pt × ℕ) (h : (sysM Γ).grp φ = (sysM Γ).grp φ') (c : Option (Fin 4)) :
    psi c φ.1 = psi c φ'.1 := by
  have h' : fM Γ.W φ = fM Γ.W φ' := h
  have hχ : chiOf φ.1 = chiOf φ'.1 := by
    have := congrArg (fun x : Label × ℕ => x.1.1.2.2) h'
    simpa [fM] using this
  rw [psi_eq_chi, psi_eq_chi, hχ]

/-- No unary link is followed by another. -/
theorem hUUU_sysM (θ : Pt × ℕ) (h : (sysM Γ).UN θ) : ¬ (sysM Γ).UN ((sysM Γ).un θ) := by
  intro h'
  obtain ⟨hj, -, -⟩ := unM_spec h
  have h0 : (Γ.unM θ).2 = 0 := h'.1
  omega

end MCtx

/-! ## The projected graph -/

/-- Projected vertices: a label (characteristic coordinates, bin) and a level. -/
abbrev MP := Label × ℕ

/-- `0` or `1`. -/
def ind (b : Bool) : ℤ := if b then 1 else 0

theorem ind_decide (P : Prop) [Decidable P] : ind (decide P) = if P then 1 else 0 := by
  unfold ind
  by_cases h : P <;> simp [h]

/-- A projected support step (a Moore displacement, a provider, an extra `e_x`, a bin step). -/
def fwdS (p : MP) (i : (Plane × Prov) × Bool × Bool) : MP :=
  (((p.1.1.1 + i.1.1.1 + ind i.2.1, p.1.1.2.1 + i.1.1.2, p.1.1.2.2 + provOff i.1.2 - vP),
    p.1.2 - ind i.2.2), p.2 - 1)

/-- A reversed projected support step. -/
def bwdS (p : MP) (i : (Plane × Prov) × Bool × Bool × Bool) : MP :=
  (((p.1.1.1 - i.1.1.1 - ind i.2.1, p.1.1.2.1 - i.1.1.2, p.1.1.2.2 - provOff i.1.2 + vP),
    p.1.2 + ind i.2.2.1), if i.2.2.2 then p.2 + 1 else p.2)

/-- A projected characteristic link (to level `T` or `1`, bin step `0` or `1`). -/
def fwdU (p : MP) (i : Bool × Bool) : MP :=
  ((p.1.1, p.1.2 - ind i.1), if i.2 then UND.Param.T else 1)

/-- A reversed projected characteristic link. -/
def bwdU (p : MP) (i : Bool) : MP := ((p.1.1, p.1.2 + ind i), 0)

/-- The index set of the projected support steps. -/
@[irreducible] def idxS : Finset ((Plane × Prov) × Bool × Bool) := (box 1 ×ˢ Finset.univ) ×ˢ Finset.univ

/-- The index set of the reversed projected support steps. -/
@[irreducible] def idxB : Finset ((Plane × Prov) × Bool × Bool × Bool) := (box 1 ×ˢ Finset.univ) ×ˢ Finset.univ

/-- **The projected memory graph** (both directions). -/
@[irreducible] def nbrM (p : MP) : Finset MP :=
  (idxS.image (fwdS p) ∪ idxB.image (bwdS p)) ∪
    ((Finset.univ : Finset (Bool × Bool)).image (fwdU p) ∪
      (Finset.univ : Finset Bool).image (bwdU p))

/-- The projected graph has degree at most `108q + 6`. -/
theorem card_nbrM_le (p : MP) : (nbrM p).card ≤ 108 * UND.Param.q + 6 := by
  have hP : (Finset.univ : Finset Prov).card = UND.Param.q := by
    rw [Finset.card_univ, card_Prov]
  have h1 : idxS.card = 36 * UND.Param.q := by
    unfold idxS
    rw [Finset.card_product, Finset.card_product, card_box_one, hP]
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
    ring
  have h2 : idxB.card = 72 * UND.Param.q := by
    unfold idxB
    rw [Finset.card_product, Finset.card_product, card_box_one, hP]
    simp only [Finset.card_univ, Fintype.card_prod, Fintype.card_bool]
    ring
  have h3 : (Finset.univ : Finset (Bool × Bool)).card = 4 := by decide
  have h4 : (Finset.univ : Finset Bool).card = 2 := by decide
  unfold nbrM
  refine (Finset.card_union_le _ _).trans ?_
  have hA := (Finset.card_union_le (idxS.image (fwdS p)) (idxB.image (bwdS p))).trans
    (Nat.add_le_add (Finset.card_image_le (s := idxS) (f := fwdS p))
      (Finset.card_image_le (s := idxB) (f := bwdS p)))
  have hB := (Finset.card_union_le ((Finset.univ : Finset (Bool × Bool)).image (fwdU p))
    ((Finset.univ : Finset Bool).image (bwdU p))).trans
    (Nat.add_le_add (Finset.card_image_le (s := Finset.univ) (f := fwdU p))
      (Finset.card_image_le (s := Finset.univ) (f := bwdU p)))
  rw [h1, h2] at hA
  rw [h3, h4] at hB
  omega

theorem nbrM_le_Delta : 108 * UND.Param.q + 6 ≤ UND.Param.Delta := by
  rw [UND.Param.Delta_eq]
  norm_num [UND.Param.q, UND.Param.K]

theorem mem_nbrM_fwdS (p : MP) {i : (Plane × Prov) × Bool × Bool} (hi : i.1.1 ∈ box 1) :
    fwdS p i ∈ nbrM p := by
  have hidx : i ∈ idxS := by
    unfold idxS
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    exact hi
  unfold nbrM
  simp only [Finset.mem_union, Finset.mem_image]
  exact Or.inl (Or.inl ⟨i, hidx, rfl⟩)

theorem mem_nbrM_bwdS (p : MP) {i : (Plane × Prov) × Bool × Bool × Bool} (hi : i.1.1 ∈ box 1) :
    bwdS p i ∈ nbrM p := by
  have hidx : i ∈ idxB := by
    unfold idxB
    simp only [Finset.mem_product, Finset.mem_univ, and_true]
    exact hi
  unfold nbrM
  simp only [Finset.mem_union, Finset.mem_image]
  exact Or.inl (Or.inr ⟨i, hidx, rfl⟩)

theorem mem_nbrM_fwdU (p : MP) (i : Bool × Bool) : fwdU p i ∈ nbrM p := by
  unfold nbrM
  simp only [Finset.mem_union, Finset.mem_image]
  exact Or.inr (Or.inl ⟨i, Finset.mem_univ _, rfl⟩)

theorem mem_nbrM_bwdU (p : MP) (i : Bool) : bwdU p i ∈ nbrM p := by
  unfold nbrM
  simp only [Finset.mem_union, Finset.mem_image]
  exact Or.inr (Or.inr ⟨i, Finset.mem_univ _, rfl⟩)

/-! ## The projection along the steps -/

theorem bin_cases {W : ℕ} (hW : 1 ≤ W) (x d : ℤ) (h0 : 0 ≤ d) (h1 : d ≤ W) :
    (x - d) / (W : ℤ) = x / W ∨ (x - d) / (W : ℤ) = x / W - 1 := by
  have hWpos : (0 : ℤ) < W := by exact_mod_cast hW
  have hle : (x - d) / (W : ℤ) ≤ x / W := Int.ediv_le_ediv hWpos (by linarith)
  have hge : (x - W) / (W : ℤ) ≤ (x - d) / W := Int.ediv_le_ediv hWpos (by linarith)
  have e : (x - W) / (W : ℤ) = x / W - 1 := by
    have := Int.add_mul_ediv_right x (-1) hWpos.ne'
    rw [show x + -1 * (W : ℤ) = x - W by ring] at this
    rw [this]
    ring
  omega

/-- The bin step as an indicator. -/
theorem bin_ind {W : ℕ} (hW : 1 ≤ W) (x d : ℤ) (h0 : 0 ≤ d) (h1 : d ≤ W) :
    (x - d) / (W : ℤ) = x / W - ind (decide ((x - d) / (W : ℤ) ≠ x / W)) := by
  rw [ind_decide]
  by_cases h : (x - d) / (W : ℤ) = x / W
  · simp [h]
  · rw [ite_eq_left h]
    exact (bin_cases hW x d h0 h1).resolve_left h

theorem fM_eq_iff (W : ℕ) (θ : Pt × ℕ) (p : MP) : fM W θ = p ↔
    θ.1.1.1.1 - outT θ = p.1.1.1 ∧ θ.1.1.1.2 = p.1.1.2.1 ∧ chiOf θ.1 = p.1.1.2.2 ∧
      outT θ / (W : ℤ) = p.1.2 ∧ θ.2 = p.2 := by
  obtain ⟨⟨⟨x, y, χ⟩, bn⟩, l⟩ := p
  simp only [fM, Prod.mk.injEq, and_assoc]

theorem outT_supOf (θ : Pt × ℕ) (p : Prov × Plane) :
    outT (supOf θ p) = outT θ - (if θ.2 ≤ 1 then 1 else 0) := by
  obtain ⟨y, j⟩ := θ
  unfold outT supOf
  simp only [par_time]
  rcases j with _ | _ | j
  · simp
  · simp
  · have h1 : ¬ (j + 2 ≤ 1) := by omega
    have h2 : j + 2 - 1 ≠ 0 := by omega
    have h3 : j + 2 ≠ 0 := by omega
    simp only [h1, h2, h3, ↓reduceIte]
    rw [show j + 2 - 1 = j + 1 by omega]
    push_cast
    ring

theorem outT_zero {θ : Pt × ℕ} (h0 : θ.2 = 0) : outT θ = θ.1.2 := by
  simp [outT, h0]

theorem outT_qV (y : Pt) : outT (qV y) = y.2 := by
  have hT : UND.Param.T ≠ 0 := by have := one_le_T; omega
  simp only [outT, qV, hT, ↓reduceIte]
  ring

theorem outT_aV (y : Pt) : outT (aV y) = y.2 := by
  simp [outT, aV]

namespace MCtx

variable {Γ : MCtx CD}

/-- **Every step of the derivation is an edge of the projected graph** (both directions). -/
theorem step_nbr (hfull : IsFullChart CD.toWangRel Γ.ref) (hW : 1 ≤ Γ.W) (a b : Pt × ℕ)
    (hab : (sysM Γ).Step a b) : fM Γ.W b ∈ nbrM (fM Γ.W a) ∧ fM Γ.W a ∈ nbrM (fM Γ.W b) := by
  rcases hab with ⟨hnf, bb, rfl⟩ | ⟨hu, rfl⟩
  · -- a support step
    set p := Γ.sel a bb with hp
    have hμ := (sel_spec hfull hnf bb).1
    show fM Γ.W (supOf a p) ∈ nbrM (fM Γ.W a) ∧ fM Γ.W a ∈ nbrM (fM Γ.W (supOf a p))
    set e : Bool := decide (a.2 ≤ 1) with he
    have ho := outT_supOf a p
    have hd0 : (0 : ℤ) ≤ (if a.2 ≤ 1 then 1 else 0) := by split_ifs <;> norm_num
    have hd1 : (if a.2 ≤ 1 then (1 : ℤ) else 0) ≤ Γ.W := by
      have : (1 : ℤ) ≤ Γ.W := by exact_mod_cast hW
      split_ifs <;> linarith
    set δ : Bool := decide (outT (supOf a p) / (Γ.W : ℤ) ≠ outT a / Γ.W) with hδ
    have hbin : outT (supOf a p) / (Γ.W : ℤ) = outT a / Γ.W - ind δ := by
      rw [hδ, ho]
      exact bin_ind hW _ _ hd0 hd1
    have hind : ind e = if a.2 ≤ 1 then 1 else 0 := ind_decide _
    have hx : (supOf a p).1.1.1.1 = a.1.1.1.1 + p.2.1 := rfl
    have hy : (supOf a p).1.1.1.2 = a.1.1.1.2 + p.2.2 := rfl
    have hχ : chiOf (supOf a p).1 = chiOf a.1 + provOff p.1 - vP := chiOf_par _ _ _
    constructor
    · have heq : fM Γ.W (supOf a p) = fwdS (fM Γ.W a) ((p.2, p.1), e, δ) := by
        rw [fM_eq_iff]
        refine ⟨?_, hy, hχ, hbin, rfl⟩
        show (supOf a p).1.1.1.1 - outT (supOf a p) = a.1.1.1.1 - outT a + p.2.1 + ind e
        rw [hx, ho, hind]
        ring
      rw [heq]
      exact mem_nbrM_fwdS _ hμ
    · have heq : fM Γ.W a =
          bwdS (fM Γ.W (supOf a p)) ((p.2, p.1), e, δ, decide (1 ≤ a.2)) := by
        rw [fM_eq_iff]
        refine ⟨?_, ?_, ?_, ?_, ?_⟩
        · show a.1.1.1.1 - outT a = (supOf a p).1.1.1.1 - outT (supOf a p) - p.2.1 - ind e
          rw [hx, ho, hind]
          ring
        · show a.1.1.1.2 = (supOf a p).1.1.1.2 - p.2.2
          rw [hy]
          ring
        · show chiOf a.1 = chiOf (supOf a p).1 - provOff p.1 + vP
          rw [hχ]
          abel
        · show outT a / (Γ.W : ℤ) = outT (supOf a p) / Γ.W + ind δ
          rw [hbin]
          ring
        · show a.2 = if decide (1 ≤ a.2) = true then (a.2 - 1) + 1 else a.2 - 1
          by_cases h1 : 1 ≤ a.2
          · simp only [h1, decide_true, ↓reduceIte]
            omega
          · simp only [h1, decide_false, Bool.false_eq_true, ↓reduceIte]
            omega
      rw [heq]
      exact mem_nbrM_bwdS _ hμ
  · -- a characteristic link
    have hL := unM_spec hu
    obtain ⟨h0, ht1, -⟩ := hu
    obtain ⟨hj1, -, hη⟩ := hL
    set η := Γ.unM a with hηdef
    have hoa : outT a = a.1.2 := outT_zero h0
    -- common shape: same characteristic, output lag `d ∈ [0, W]`, level `1` or `T`
    have key : ∀ d : ℤ, 0 ≤ d → d ≤ Γ.W → η.1.1.1.1 - outT η = a.1.1.1.1 - outT a →
        η.1.1.1.2 = a.1.1.1.2 → chiOf η.1 = chiOf a.1 → outT η = outT a - d →
        (η.2 = UND.Param.T ∨ η.2 = 1) →
        fM Γ.W η ∈ nbrM (fM Γ.W a) ∧ fM Γ.W a ∈ nbrM (fM Γ.W η) := by
      intro d hd0 hd1 hx hy hχ hout hlev
      set δ : Bool := decide (outT η / (Γ.W : ℤ) ≠ outT a / Γ.W) with hδ
      have hbin : outT η / (Γ.W : ℤ) = outT a / Γ.W - ind δ := by
        rw [hδ, hout]
        exact bin_ind hW _ _ hd0 hd1
      constructor
      · have heq : fM Γ.W η = fwdU (fM Γ.W a) (δ, decide (η.2 = UND.Param.T)) := by
          rw [fM_eq_iff]
          refine ⟨hx, hy, hχ, hbin, ?_⟩
          show η.2 = if decide (η.2 = UND.Param.T) = true then UND.Param.T else 1
          by_cases hT : η.2 = UND.Param.T
          · simp [hT]
          · simp only [hT, decide_false, Bool.false_eq_true, ↓reduceIte]
            exact hlev.resolve_left hT
        rw [heq]
        exact mem_nbrM_fwdU _ _
      · have heq : fM Γ.W a = bwdU (fM Γ.W η) δ := by
          rw [fM_eq_iff]
          refine ⟨hx.symm, hy.symm, hχ.symm, ?_, h0⟩
          show outT a / (Γ.W : ℤ) = outT η / Γ.W + ind δ
          rw [hbin]
          ring
        rw [heq]
        exact mem_nbrM_bwdU _ _
    have hW' : (1 : ℤ) ≤ Γ.W := by exact_mod_cast hW
    rcases hη with he | ⟨i, hi, he | he⟩
    · refine key 0 le_rfl (by linarith) ?_ ?_ ?_ ?_ (Or.inl ?_)
      · rw [he, outT_qV, qV_planar, hoa]
      · rw [he]; simp [qV, qShift]
      · rw [he, chiOf_qV]
      · rw [he, outT_qV, hoa]; ring
      · rw [he]; rfl
    · have hi' : ((i : ℤ) + 1) ≤ Γ.W := by exact_mod_cast hi
      refine key ((i : ℤ) + 1) (by positivity) hi' ?_ ?_ ?_ ?_ (Or.inr ?_)
      · rw [he, outT_aV, hoa]
        simp only [aV, rideBase]
        ring
      · rw [he]; rfl
      · rw [he]; exact chiOf_rideBase _ _
      · rw [he, outT_aV, hoa]
        simp only [rideBase]
        ring
      · rw [he]; rfl
    · have hi' : ((i : ℤ) + 1) ≤ Γ.W := by exact_mod_cast hi
      refine key ((i : ℤ) + 1) (by positivity) hi' ?_ ?_ ?_ ?_ (Or.inl ?_)
      · rw [he, outT_qV, qV_planar, hoa]
        simp only [rideBase]
        ring
      · rw [he]; simp [qV, qShift, rideBase]
      · rw [he, chiOf_qV]; exact chiOf_rideBase _ _
      · rw [he, outT_qV, hoa]
        simp only [rideBase]
        ring
      · rw [he]; rfl

/-- Reached vertices are bad. -/
theorem bad_of_reach (hfull : IsFullChart CD.toWangRel Γ.ref) {a b : Pt × ℕ}
    (h : (sysM Γ).Reach a b) (ha : Γ.Bad a) : Γ.Bad b := by
  induction h with
  | refl => exact ha
  | tail _ hst ih =>
    rcases hst with ⟨hnf, bb, rfl⟩ | ⟨hu, rfl⟩
    · exact (sel_spec hfull hnf bb).2
    · exact (unM_spec hu).2.1

end MCtx

/-! ## Lemma 7.1: the terminal sources -/

/-- A flag among the atoms `L` makes the trivial-mark ride event hold. -/
theorem mem_rideEv_true {I β : Type*} (ω : I → Bool × β) :
    ∀ (L : List I) (x : I), x ∈ L → (ω x).1 = true → ω ∈ RideEv (fun _ : β => true) L
  | [], x, h, _ => by simp at h
  | b :: L, x, h, hf => by
    by_cases hb : (ω b).1 = true
    · exact Or.inl ⟨hb, rfl⟩
    · have hb' : (ω b).1 = false := by simpa using hb
      rcases List.mem_cons.1 h with rfl | h
      · exact absurd hf hb
      · exact Or.inr ⟨hb', mem_rideEv_true ω L x h hf⟩

namespace MCtx

/-- **The hypotheses of Lemma 7.1**: the chart is a full legal chart; the helpers follow (4) off
flags at every integer time (`HelperTraj`); unflagged data at positive times are the proposal's;
the data are the chart at times `≤ 0`; at a live phase-zero `End` of the chart there is a finite
phase-zero gate of depth `d` (`d ≥ k`), with row flag `[d < a]` and its origin exactly `ℓ_d` sites
back on the row; short rides fit in a bin (`ℓ_d ≤ W`, `d < a`), long origins lie outside the recent
window (`W < ℓ_d`, `d ≥ a`). -/
structure Hyp (Γ : MCtx CD) (s : ℕ) (tc tr : ℕ → Bool) (k a : ℕ) : Prop where
  full : IsFullChart CD.toWangRel Γ.ref
  helper : HelperTraj s Γ.Y Γ.ω
  dyn : ∀ t : ℤ, 1 ≤ t → ∀ w, flagAt Γ.ω t w = false →
    dataOf (Γ.Y t) w = (proposal s (Γ.Y (t - 1)) w).1
  init : ∀ t : ℤ, t ≤ 0 → ∀ w, dataOf (Γ.Y t) w = some (Γ.ref w.1)
  gate : ∀ ξ : Plane, CD.phase (ctr CD.toWangRel (Γ.ref ξ)) = 0 →
    CD.endP (ctr CD.toWangRel (Γ.ref ξ)) = true → ∃ d, k ≤ d ∧
      IsLeftEnd (phaseOffsets tr) d ξ.2 ∧ IsRightEnd (phaseOffsets tc) d ξ.1 ∧
      CD.hrow (ctr CD.toWangRel (Γ.ref ξ)) = decide (d < a) ∧
      ∀ i : ℕ, i ≤ UND.Windows.ell d →
        CD.orig (ctr CD.toWangRel (Γ.ref (ξ.1 - i, ξ.2))) = decide (i = UND.Windows.ell d)
  short : ∀ d, d < a → UND.Windows.ell d ≤ Γ.W
  long : ∀ d, a ≤ d → Γ.W < UND.Windows.ell d

variable {Γ : MCtx CD}

theorem bad_zero_iff (w : ISite) (t : ℤ) :
    Γ.Bad ((w, t), 0) ↔ dataOf (Γ.Y t) w ≠ some (Γ.ref w.1) := by
  unfold Bad val
  simp

theorem drvA_good {y : Pt} (h : ¬ Γ.Bad (aV y)) :
    drvA (Γ.Y (y.2 - 1)) y.1 = some (Γ.ref y.1.1) := by
  unfold Bad at h
  rw [val_aV] at h
  exact not_not.1 h

theorem drvQ_good {y : Pt} (h : ¬ Γ.Bad (qV y)) :
    drvQ (Γ.Y (y.2 - 1)) y.1 = some (Γ.ref y.1.1) := by
  unfold Bad at h
  rw [val_qV, qV_planar] at h
  exact not_not.1 h

theorem chSite_ride_planar (w : ISite) (t : ℤ) (i : ℕ) :
    (chSite (w.1.1 - t) w.1.2 (w.2 + t • vP) (t - 1 - i)).1 = (w.1.1 - ((i + 1 : ℕ) : ℤ), w.1.2) :=
  Prod.ext (by simp only [chSite]; push_cast; ring) rfl

/-- **Lemma 7.1, the terminal sources**: a bad terminal leaf is at level `0` and is either a
flagged output (a raw source of its label) or an erasure at a correct gate whose intrinsic bad
event holds (a statistical source of its label). -/
theorem term_source {s : ℕ} {tc tr : ℕ → Bool} {k a : ℕ} (hH : Hyp Γ s tc tr k a)
    (hW : 1 ≤ Γ.W) {φ : Pt × ℕ} (hb : Γ.Bad φ) (ht : (sysM Γ).IsTerm φ) :
    φ.2 = 0 ∧ Γ.ω ∈ RawEv CD Γ.W (fM Γ.W φ).1 ∪ StatEv CD tc tr k s a Γ.W (fM Γ.W φ).1 := by
  classical
  obtain ⟨⟨w, t⟩, j⟩ := φ
  have hnf : ¬ (Γ.NFv ((w, t), j) ∨ Γ.NFd ((w, t), j)) := ht.1
  have hun : ¬ Γ.UNd ((w, t), j) := ht.2
  have hj : j = 0 := by
    by_contra hj
    exact hnf (Or.inl ⟨Nat.one_le_iff_ne_zero.2 hj, hb⟩)
  subst hj
  refine ⟨rfl, ?_⟩
  have hbad : dataOf (Γ.Y t) w ≠ some (Γ.ref w.1) := (bad_zero_iff w t).1 hb
  have ht1 : 1 ≤ t := by
    by_contra h
    exact hbad (hH.init t (by omega) w)
  have hlab : (fM Γ.W ((w, t), 0)).1 = ((w.1.1 - t, w.1.2, w.2 + t • vP), t / (Γ.W : ℤ)) := by
    simp [fM, outT, chiOf]
  rw [hlab]
  have hWz : (0 : ℤ) < Γ.W := by exact_mod_cast hW
  have he0 := Int.emod_nonneg t hWz.ne'
  have he1 := Int.emod_lt_of_pos t hWz
  have hi0W : (t % (Γ.W : ℤ)).toNat < Γ.W := by omega
  have htime : t / (Γ.W : ℤ) * Γ.W + (((t % (Γ.W : ℤ)).toNat : ℕ) : ℤ) = t := by
    have h3 := Int.ediv_mul_add_emod t (Γ.W : ℤ)
    rw [Int.toNat_of_nonneg he0]
    linarith
  have hsite : chSite (w.1.1 - t) w.1.2 (w.2 + t • vP) t = w := chSite_self w t
  by_cases hfl : flagAt Γ.ω t w = true
  · left
    refine mem_rideEv_true Γ.ω _ (laneAtom (w.1.1 - t) w.1.2 (w.2 + t • vP) 0 t) ?_ ?_
    · unfold rawList
      refine List.mem_map.2 ⟨(t % (Γ.W : ℤ)).toNat, List.mem_range.2 hi0W, ?_⟩
      show laneAtom (w.1.1 - t) w.1.2 (w.2 + t • vP) 0
        (t / (Γ.W : ℤ) * Γ.W + (((t % (Γ.W : ℤ)).toNat : ℕ) : ℤ)) =
        laneAtom (w.1.1 - t) w.1.2 (w.2 + t • vP) 0 t
      rw [htime]
    · show (Γ.ω (t, siteEquiv.symm
        (chSite (w.1.1 - t) (w.1.2 + ((0 : ℕ) : ℤ)) (w.2 + t • vP) t))).1 = true
      rw [Nat.cast_zero, add_zero, hsite]
      exact hfl
  · right
    have hfl' : flagAt Γ.ω t w = false := by simpa using hfl
    have hFl : ¬ Γ.Fl ((w, t), 0) := hfl
    have hA : ¬ Γ.Bad (aV (w, t)) := fun h => hnf (Or.inr ⟨rfl, ht1, hb, hFl, h⟩)
    have hlink : ∀ η, ¬ Γ.Link ((w, t), 0) η := fun η h => hun ⟨rfl, ht1, hb, hFl, hA, η, h⟩
    have hQb : ¬ Γ.Bad (qV (w, t)) := fun h => hlink _ ⟨one_le_T, h, Or.inl rfl⟩
    have hdA := drvA_good hA
    have hdQ := drvQ_good hQb
    dsimp only at hdA hdQ
    have hPin : Pin s (Γ.Y (t - 1)) w := by
      by_contra hP
      apply hbad
      rw [hH.dyn t ht1 w hfl']
      simp only [proposal, hP, ↓reduceIte]
      exact hdA
    rcases hPin with hnone | ⟨Q', hQ', hph, hend, hcnt⟩
    · rw [hdQ] at hnone
      exact absurd hnone (by simp)
    · rw [hdQ] at hQ'
      have hQe : Q' = Γ.ref w.1 := (Option.some_inj.1 hQ').symm
      subst hQe
      obtain ⟨d, hkd, hLe, hRe, hrow, horig⟩ := hH.gate w.1 hph hend
      have hell := UND.Windows.ell_pos d
      -- the drivers along the ride are correct
      have hgood : ∀ i : ℕ, i < Γ.W → i + 1 ≤ UND.Windows.ell d →
          LiveAt Γ.Y (w.1.1 - t) w.1.2 (w.2 + t • vP) (t - 1 - i)
            (decide (i + 1 = UND.Windows.ell d)) := by
        intro i hi hid
        have hA' : ¬ Γ.Bad (aV (rideBase (w, t) i)) :=
          fun h => hlink _ ⟨le_rfl, h, Or.inr ⟨i, hi, Or.inl rfl⟩⟩
        have hQ'' : ¬ Γ.Bad (qV (rideBase (w, t) i)) :=
          fun h => hlink _ ⟨one_le_T, h, Or.inr ⟨i, hi, Or.inr rfl⟩⟩
        have h1 := drvA_good hA'
        have h2 := drvQ_good hQ''
        rw [rideBase_eq] at h1 h2
        dsimp only at h1 h2
        refine ⟨_, _, h1, h2, ?_⟩
        rw [chSite_ride_planar]
        exact horig (i + 1) hid
      have hgate : LiveAt Γ.Y (w.1.1 - t) w.1.2 (w.2 + t • vP) t false := by
        refine ⟨_, _, by rw [hsite]; exact hdA, by rw [hsite]; exact hdQ, ?_⟩
        have ho := horig 0 (Nat.zero_le _)
        have e : ((w.1.1 - ((0 : ℕ) : ℤ), w.1.2) : Plane) = w.1 := by simp
        rw [e] at ho
        rw [ho]
        simp only [decide_eq_false_iff_not]
        omega
      refine ⟨d, (t % (Γ.W : ℤ)).toNat, hi0W, ?_, ?_⟩
      · show IsGate tc tr k d (w.1.1 - t) w.1.2
          (t / (Γ.W : ℤ) * Γ.W + (((t % (Γ.W : ℤ)).toNat : ℕ) : ℤ))
        rw [htime]
        refine ⟨hkd, hLe, ?_⟩
        rw [sub_add_cancel]
        exact hRe
      · show Γ.ω ∈ GateBad CD s a Γ.W d (w.1.1 - t) w.1.2 (w.2 + t • vP)
          (t / (Γ.W : ℤ) * Γ.W + (((t % (Γ.W : ℤ)).toNat : ℕ) : ℤ))
        rw [htime]
        unfold GateBad
        by_cases hda : d < a
        · simp only [hda, ↓reduceIte]
          have hrow' : CD.hrow (ctr CD.toWangRel (Γ.ref w.1)) = true := by
            rw [hrow]
            simp [hda]
          have hs : s ≤ hcount (Γ.Y (t - 1)) w := by
            rcases hcnt with ⟨-, h⟩ | ⟨h, -⟩
            · exact h
            · rw [hrow'] at h
              exact absurd h (by simp)
          have hshort := hH.short d hda
          have hcopy : ∀ i < UND.Windows.ell d - 1,
              LiveAt Γ.Y (w.1.1 - t) w.1.2 (w.2 + t • vP) (t - 1 - i) false := by
            intro i hi
            have := hgood i (by omega) (by omega)
            rwa [show decide (i + 1 = UND.Windows.ell d) = false by
              simp only [decide_eq_false_iff_not]; omega] at this
          have horig' : LiveAt Γ.Y (w.1.1 - t) w.1.2 (w.2 + t • vP)
              (t - 1 - ((UND.Windows.ell d - 1 : ℕ) : ℤ)) true := by
            have := hgood (UND.Windows.ell d - 1) (by omega) (by omega)
            rwa [show decide (UND.Windows.ell d - 1 + 1 = UND.Windows.ell d) = true by
              simp only [decide_eq_true_eq]; omega] at this
          have hc' := hcount_short hH.helper (UND.Windows.ell d - 1) hgate hcopy horig'
          rw [hsite, show UND.Windows.ell d - 1 + 1 = UND.Windows.ell d by omega] at hc'
          show s ≤ laneCount _ (w.1.1 - t) w.1.2 (w.2 + t • vP) t (UND.Windows.ell d) Γ.ω
          rw [← hc']
          exact hs
        · simp only [hda, ↓reduceIte]
          have hrow' : CD.hrow (ctr CD.toWangRel (Γ.ref w.1)) = false := by
            rw [hrow]
            simp [hda]
          have hl : lcount (Γ.Y (t - 1)) w < s := by
            rcases hcnt with ⟨h, -⟩ | ⟨-, h⟩
            · rw [hrow'] at h
              exact absurd h (by simp)
            · exact h
          have hlong := hH.long d (by omega)
          have hcopy : ∀ i < Γ.W,
              LiveAt Γ.Y (w.1.1 - t) w.1.2 (w.2 + t • vP) (t - 1 - i) false := by
            intro i hi
            have := hgood i hi (by omega)
            rwa [show decide (i + 1 = UND.Windows.ell d) = false by
              simp only [decide_eq_false_iff_not]; omega] at this
          have hc' := lcount_long hH.helper Γ.W hgate hcopy
          rw [hsite] at hc'
          show laneCount _ (w.1.1 - t) w.1.2 (w.2 + t • vP) t Γ.W Γ.ω < s
          exact lt_of_le_of_lt hc' hl

/-- **Lemmas 7.1 and 7.2**: a data error at `(w, t)` has a literal encoding at the projected root
in the graph `nbrM` (degree `≤ 108q + 6 ≤ Δ`), with `g ≥ 1` distinct labels, at most `256g`
edges, every label at level `0` and a raw or statistical source of its bin. -/
theorem mem_cover {s : ℕ} {tc tr : ℕ → Bool} {k a : ℕ} (hH : Hyp Γ s tc tr k a) (hW : 1 ≤ Γ.W)
    (w : ISite) (t : ℤ) (hbad : dataOf (Γ.Y t) w ≠ some (Γ.ref w.1)) :
    ∃ g, 1 ≤ g ∧ ∃ K A, UND.Counting.IsEncoding nbrM (fM Γ.W ((w, t), 0)) (256 * g) K A ∧
      (A.image id).card = g ∧
      ∀ v ∈ A, v.2 = 0 ∧ Γ.ω ∈ RawEv CD Γ.W v.1 ∪ StatEv CD tc tr k s a Γ.W v.1 := by
  classical
  obtain ⟨g, hg, K, A, hM⟩ := (sysM Γ).mem_encoding (by simp) (isPotential_sysM hH.full)
    (fun φ φ' _ _ h c => hgrp_sysM φ φ' h c) (fun θ h1 h2 => absurd h2 (hUUU_sysM θ h1))
    nbrM (fM Γ.W) id (fun _ _ => rfl) (fun a b hab _ => step_nbr hH.full hW a b hab)
    (fun φ φ' _ _ h hne => absurd h hne) ((w, t), 0)
  refine ⟨g, hg, K, A, GroupedSystem.MemEnc.isEncoding (sysM Γ) hM, hM.2.2.2.2.1,
    fun v hv => ?_⟩
  obtain ⟨φ, hr, htm, rfl⟩ := hM.2.2.2.2.2 v hv
  have hb := bad_of_reach hH.full hr ((bad_zero_iff w t).2 hbad)
  exact term_source hH hW hb htm

end MCtx



end UND.Memory
