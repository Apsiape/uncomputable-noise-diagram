/-
# Section 2.2: interval fields, drivers, `Pin` and the proposal (R3, R4)

Nodes R3, R4 of `BLUEPRINT.md` (Part A.2), NEW. Generic in the chart tile set (D4): the routing
alphabet `R` of Section 3 enters through `ChartData`, a tile set with matching relations and the
four tile functions read by the controller (`Orig`, `End`, `H_row`, the lane phase `p`), and in
the constants `B` and `s` (selected in Section 9; kernel discipline D13: never instantiated here).

Paper (Section 2.2): "The helper alphabet `ℋ` has 100 letters: LOW represents `{0}`, UNKNOWN
represents `{0,1}`, and 98 HIGH aliases represent `{1}`. Fix one representative for each of these
three intervals. The physical alphabet is `Σ = 𝒜_R × 𝒜_R × ℋ^B` (2). … At proposal time `t` put
`A_t = F_R(D_{t-1})`, `Q_t(u,P) = F_R^T(D_{t-1})(u, P - (T-1)v)` (3). … For a physical site `w`,
field `j` always uses the base `z = w - j e_y`. Its provisional interval is (4) … At a base `w`,
let `h_w` count the provisional intervals `J_{j,t}(w + j e_y)` containing `1`, and `l_w` those
equal to `{1}`. … (5) `Pin` … (6) the deterministic proposed symbol
`(⊥ if Pin else A_t(w), A_t(w), (rep J_{j,t}(w))_{j<B})`."

* `Ival` (the three represented intervals), `Helper = Fin 100` with `rep` (`0` LOW, `1` UNKNOWN,
  `2 … 99` HIGH) and the representatives `Ival.repr`; `rep_repr`; the counts `1`, `1`, `98`;
* `ChartData B τ` (a `WangRel` with `orig`, `endP`, `hrow : τ → Bool`, `phase : τ → ZMod B`);
* `PhysSym` (2), `drvA`, `drvQ` (3), `Jf` (4), `hcount`, `lcount`, `Pin` (5), **`proposal`** (6);
* translation commutation **`proposal_translate`**, and locality **`proposal_local`** on the finite
  neighbourhood `nbhdP` (bases `w - j e_y`, `j < B`, with the ordinary query box `Mo × S` and the
  deep query box `[-T, T]² × (-(T-1)v + [0, 175T]⁴)`, and the `B` helper sites
  `w + j e_y - e_x + v`), with **`card_nbhdP_le`**: `|N| ≤ B(n_A + n_Q) + B ≤ B(n_A + n_Q + 2)`
  (Prop 2.1's count; the helper count is `B`, one less than the printed `B + 1`).
-/
import UncomputableNoiseDiagram.Rule.Checker
import Mathlib.Data.ZMod.Defs
import Mathlib.Tactic.Abel

set_option autoImplicit false
set_option linter.unusedSectionVars false

noncomputable section

namespace UND.Rule

open FNE (Plane box Cell mooreDirs)

/- Kernel/elaborator discipline (D13, extended): `T = 500` is kept opaque here, otherwise
unification unfolds `F_R^[T]` five hundred times (or the box `[-T, T]²`) and hits the recursion
limit. -/
attribute [local irreducible] UND.Param.T

/-! ## R3: the helper alphabet -/

/-- The three represented intervals `{0}`, `{0,1}`, `{1}`. -/
inductive Ival where
  | zero
  | both
  | one
  deriving DecidableEq

namespace Ival

/-- `1 ∈ I`. -/
def hasOne : Ival → Bool
  | zero => false
  | both => true
  | one => true

/-- `{0} ∪ I`. -/
def withZero : Ival → Ival
  | zero => zero
  | both => both
  | one => both

/-- The fixed representative of an interval: LOW `0`, UNKNOWN `1`, HIGH `2`. -/
def repr : Ival → Fin 100
  | zero => 0
  | both => 1
  | one => 2

end Ival

/-- The helper alphabet `ℋ`: 100 letters. -/
abbrev Helper := Fin 100

/-- The represented interval of a helper letter: `0` is LOW (`{0}`), `1` is UNKNOWN (`{0,1}`), the
98 letters `2, …, 99` are HIGH aliases (`{1}`). -/
def Helper.rep (a : Helper) : Ival :=
  if a.val = 0 then .zero else if a.val = 1 then .both else .one

theorem Helper.rep_repr (I : Ival) : Helper.rep I.repr = I := by
  cases I <;> rfl

/-- One LOW letter, one UNKNOWN letter, 98 HIGH aliases. -/
theorem Helper.card_rep :
    (Finset.univ.filter (fun a : Helper => Helper.rep a = .zero)).card = 1 ∧
    (Finset.univ.filter (fun a : Helper => Helper.rep a = .both)).card = 1 ∧
    (Finset.univ.filter (fun a : Helper => Helper.rep a = .one)).card = 98 := by
  decide

/-! ## The chart data read by the controller -/

/-- The chart alphabet as seen by the rule: a tile set with matching relations (D4) and the tile
functions `Orig`, `End`, `H_row` and the lane phase `p ∈ ℤ/Bℤ` (Section 3), read on the central
tile of a live letter. -/
structure ChartData (B : ℕ) (τ : Type*) extends WangRel τ where
  /-- `Orig`: a bottom light horizontal wall meets a left light vertical wall -/
  orig : τ → Bool
  /-- `End`: a bottom light horizontal wall meets a right light vertical wall -/
  endP : τ → Bool
  /-- the row flag `H_row` -/
  hrow : τ → Bool
  /-- the lane phase `p` -/
  phase : τ → ZMod B

variable {B : ℕ} {τ : Type*} [Fintype τ] [DecidableEq τ] (CD : ChartData B τ)

/-- (2): the physical alphabet `Σ = 𝒜_R × 𝒜_R × ℋ^B` (data `D`, second coordinate `H`, fields
`I_0, …, I_{B-1}`). -/
abbrev PhysSym := ChartSym CD.toWangRel × ChartSym CD.toWangRel × (Fin B → Helper)

/-- Physical configurations on `ℤ² × ℤ⁴`. -/
abbrev PConfig := ISite → PhysSym CD

/-! ## R4: drivers, fields, `Pin`, the proposal -/

/-- The planar unit vector `e_x`. -/
def ex : ISite := ((1, 0), 0)

/-- `j e_y`. -/
def jy (j : ℕ) : ISite := ((0, (j : ℤ)), 0)

/-- `v = (32, 32, 32, 32)`, a provider vector (changes only `P`). -/
def vS : ISite := (0, fun _ => 32)

/-- The provider part `(T - 1)v` of the recentering. -/
def qOff : Fin 4 → ℤ := fun _ => 32 * ((UND.Param.T : ℤ) - 1)

/-- The recentering `(T - 1)v` of the deep query. -/
def qShift : ISite := (0, qOff)

variable {CD}

/-- The data coordinate `D`. -/
def dataOf (x : PConfig CD) : ISite → ChartSym CD.toWangRel := fun w => (x w).1

/-- The helper field `I_j`. -/
def fieldOf (x : PConfig CD) (j : Fin B) (w : ISite) : Helper := (x w).2.2 j

/-- (3): the ordinary driver `A_t = F_R(D_{t-1})`. -/
def drvA (x : PConfig CD) : ISite → ChartSym CD.toWangRel := FR CD.toWangRel (dataOf x)

/-- (3): the deep driver `Q_t(u, P) = F_R^T(D_{t-1})(u, P - (T-1)v)`. -/
def drvQ (x : PConfig CD) : ISite → ChartSym CD.toWangRel :=
  fun w => (FR CD.toWangRel)^[UND.Param.T] (dataOf x) (w - qShift)

/-- (4) as a function of the drivers at the base and the old field at `w - e_x + v`. -/
def Jof (a q : ChartSym CD.toWangRel) (old : Helper) : Ival :=
  match a, q with
  | none, _ => .both
  | some _, none => (Helper.rep old).withZero
  | some _, some Q => if CD.orig (ctr CD.toWangRel Q) then .zero else Helper.rep old

/-- (4): the provisional interval `J_{j,t}(w)`, base `z = w - j e_y`. -/
def Jf (x : PConfig CD) (j : Fin B) (w : ISite) : Ival :=
  Jof (drvA x (w - jy j)) (drvQ x (w - jy j)) (fieldOf x j (w - ex + vS))

/-- `h_w`: the provisional intervals `J_{j,t}(w + j e_y)` containing `1`. -/
def hcount (x : PConfig CD) (w : ISite) : ℕ :=
  (Finset.univ.filter (fun j : Fin B => (Jf x j (w + jy j)).hasOne = true)).card

/-- `l_w`: the provisional intervals `J_{j,t}(w + j e_y)` equal to `{1}`. -/
def lcount (x : PConfig CD) (w : ISite) : ℕ :=
  (Finset.univ.filter (fun j : Fin B => Jf x j (w + jy j) = .one)).card

/-- (5): `Pin_t(w) = 1` iff `Q_t(w) = ⊥`, or `Q_t(w)` is live with `p = 0`, `End`, and
(`H_row = 1` and `h_w ≥ s`) or (`H_row = 0` and `l_w < s`). -/
def Pin (s : ℕ) (x : PConfig CD) (w : ISite) : Prop :=
  drvQ x w = none ∨ ∃ Q, drvQ x w = some Q ∧ CD.phase (ctr CD.toWangRel Q) = 0 ∧
    CD.endP (ctr CD.toWangRel Q) = true ∧
    ((CD.hrow (ctr CD.toWangRel Q) = true ∧ s ≤ hcount x w) ∨
      (CD.hrow (ctr CD.toWangRel Q) = false ∧ lcount x w < s))

open Classical in
/-- **(6): the deterministic proposed symbol**
`(⊥ if Pin else A_t(w), A_t(w), (rep J_{j,t}(w))_{j<B})`. -/
def proposal (s : ℕ) (x : PConfig CD) : PConfig CD := fun w =>
  (if Pin s x w then none else drvA x w, drvA x w, fun j => (Jf x j w).repr)

/-! ## Translation commutation -/

theorem drvA_translate (x : PConfig CD) (a : ISite) :
    drvA (fun w => x (w + a)) = fun w => drvA x (w + a) :=
  FR_translate CD.toWangRel (dataOf x) a

theorem drvQ_translate (x : PConfig CD) (a : ISite) :
    drvQ (fun w => x (w + a)) = fun w => drvQ x (w + a) := by
  funext w
  unfold drvQ
  have := congrFun (FR_iter_translate CD.toWangRel UND.Param.T (dataOf x) a) (w - qShift)
  rw [← sub_add_eq_add_sub]
  exact this

theorem Jf_translate (x : PConfig CD) (a : ISite) (j : Fin B) (w : ISite) :
    Jf (fun w => x (w + a)) j w = Jf x j (w + a) := by
  unfold Jf
  rw [drvA_translate, drvQ_translate]
  simp only [fieldOf]
  have e1 : w - jy j + a = w + a - jy j := sub_add_eq_add_sub _ _ _
  have e2 : w - ex + vS + a = w + a - ex + vS := by abel
  rw [e1, e2]

theorem hcount_translate (x : PConfig CD) (a w : ISite) :
    hcount (fun w => x (w + a)) w = hcount x (w + a) := by
  unfold hcount
  congr 1
  refine Finset.filter_congr (fun j _ => ?_)
  rw [Jf_translate, add_right_comm]

theorem lcount_translate (x : PConfig CD) (a w : ISite) :
    lcount (fun w => x (w + a)) w = lcount x (w + a) := by
  unfold lcount
  congr 1
  refine Finset.filter_congr (fun j _ => ?_)
  rw [Jf_translate, add_right_comm]

theorem Pin_translate (s : ℕ) (x : PConfig CD) (a w : ISite) :
    Pin s (fun w => x (w + a)) w ↔ Pin s x (w + a) := by
  unfold Pin
  rw [drvQ_translate, hcount_translate, lcount_translate]

/-- **The proposal commutes with every translation of `ℤ² × ℤ⁴`.** -/
theorem proposal_translate (s : ℕ) (x : PConfig CD) (a : ISite) :
    proposal s (fun w => x (w + a)) = fun w => proposal s x (w + a) := by
  classical
  funext w
  unfold proposal
  simp only [Pin_translate, drvA_translate, Jf_translate]

/-! ## Locality and the neighbourhood (Prop 2.1) -/

/-- The ordinary query box `Mo × S` (relative to a base). Irreducible: the concrete finsets of
this section must never be evaluated by unification. -/
@[irreducible] def nbhdA : Finset ISite := box 1 ×ˢ (Finset.univ.image provOff)

/-- The provider-coordinate box of the deep query: `-(T-1)v + [0, 175T]⁴`. -/
@[irreducible] def cubeQ : Finset (Fin 4 → ℤ) :=
  Fintype.piFinset (fun _ => Finset.Icc (-(32 * ((UND.Param.T : ℤ) - 1)))
    (-(32 * ((UND.Param.T : ℤ) - 1)) + 175 * UND.Param.T))

/-- The deep query box `[-T, T]² × (-(T-1)v + [0, 175T]⁴)` (relative to a base). -/
@[irreducible] def nbhdQ : Finset ISite := box UND.Param.T ×ˢ cubeQ

/-- The neighbourhood of the proposal: the query boxes at the `B` bases `-j e_y` and the `B` helper
sites `j e_y - e_x + v`. -/
@[irreducible] def nbhdP (B : ℕ) : Finset ISite :=
  (Finset.range B).biUnion (fun j => (nbhdA ∪ nbhdQ).image (fun z => z - jy j)) ∪
    (Finset.range B).image (fun j => jy j - ex + vS)

theorem card_nbhdA_le : nbhdA.card ≤ UND.Param.nA := by
  unfold nbhdA UND.Param.nA
  rw [Finset.card_product]
  have h1 : (box 1).card = 9 := by decide
  have h2 : (Finset.univ.image provOff).card ≤ UND.Param.q :=
    Finset.card_image_le.trans (by rw [Finset.card_univ, card_Prov])
  rw [h1]
  omega

theorem card_box (n : ℕ) : (box n).card = (2 * n + 1) ^ 2 := by
  unfold box
  rw [Finset.card_product, Int.card_Icc, sq]
  congr 1 <;> omega

theorem card_nbhdQ : nbhdQ.card = UND.Param.nQ := by
  unfold nbhdQ cubeQ UND.Param.nQ
  rw [Finset.card_product, card_box, Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 2
  simp only [UND.Param.L, UND.Param.m]
  omega

/-- **Prop 2.1's count**: `|N| ≤ B(n_A + n_Q) + B ≤ B(n_A + n_Q + 2)`. -/
theorem card_nbhdP_le (B : ℕ) :
    (nbhdP B).card ≤ B * (UND.Param.nA + UND.Param.nQ) + B ∧
      (nbhdP B).card ≤ B * (UND.Param.nA + UND.Param.nQ + 2) := by
  unfold nbhdP
  have h1 : ((Finset.range B).biUnion
      (fun j => (nbhdA ∪ nbhdQ).image (fun z => z - jy j))).card ≤
      B * (UND.Param.nA + UND.Param.nQ) := by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ j ∈ Finset.range B, ((nbhdA ∪ nbhdQ).image (fun z => z - jy j)).card
        ≤ ∑ _j ∈ Finset.range B, (UND.Param.nA + UND.Param.nQ) := by
          refine Finset.sum_le_sum (fun j _ => Finset.card_image_le.trans
            ((Finset.card_union_le _ _).trans ?_))
          rw [card_nbhdQ]
          exact Nat.add_le_add_right card_nbhdA_le _
      _ = B * (UND.Param.nA + UND.Param.nQ) := by
          rw [Finset.sum_const, Finset.card_range, smul_eq_mul]
  have h2 : ((Finset.range B).image (fun j => jy j - ex + vS)).card ≤ B :=
    Finset.card_image_le.trans (by rw [Finset.card_range])
  have h := (Finset.card_union_le _ _).trans (Nat.add_le_add h1 h2)
  refine ⟨h, h.trans ?_⟩
  nlinarith

/-- The data reads of the ordinary driver lie in `nbhdA`. -/
theorem drvA_congr {x y : PConfig CD} {b : ISite}
    (h : ∀ z ∈ nbhdA, (x (b + z)).1 = (y (b + z)).1) : drvA x b = drvA y b := by
  unfold drvA
  refine FR_local CD.toWangRel (fun d hd π => ?_)
  have hmem : ((d, provOff π) : ISite) ∈ nbhdA := by
    unfold nbhdA
    exact Finset.mem_product.mpr ⟨hd, Finset.mem_image_of_mem provOff (Finset.mem_univ π)⟩
  exact h _ hmem

theorem mem_cubeQ {o : Fin 4 → ℤ} (ho : InCube (175 * (UND.Param.T : ℕ)) o) :
    o - qOff ∈ cubeQ := by
  unfold cubeQ
  rw [Fintype.mem_piFinset]
  intro j
  have := ho j
  simp only [Pi.sub_apply, Finset.mem_Icc, qOff]
  constructor <;> linarith [this.1, this.2]

/-- The data reads of the deep driver lie in `nbhdQ`. -/
theorem drvQ_congr {x y : PConfig CD} {b : ISite}
    (h : ∀ z ∈ nbhdQ, (x (b + z)).1 = (y (b + z)).1) : drvQ x b = drvQ y b := by
  unfold drvQ
  refine FR_iter_local CD.toWangRel UND.Param.T (fun d hd o ho => ?_)
  have hmem : ((d, o - qOff) : ISite) ∈ nbhdQ := by
    unfold nbhdQ
    exact Finset.mem_product.mpr ⟨hd, mem_cubeQ ho⟩
  have hz := h (d, o - qOff) hmem
  have e : b + ((d, o - qOff) : ISite) = ((b - qShift).1 + d, (b - qShift).2 + o) := by
    refine Prod.ext ?_ ?_
    · simp [qShift]
    · simp only [qShift, Prod.snd_add, Prod.snd_sub]
      abel
  rw [e] at hz
  exact hz

/-- **Locality of the proposal** (Prop 2.1): for `B ≥ 1` (so that the base `w` itself is among the
`B` bases), `proposal x w` reads only `x` on `w + N`. -/
theorem proposal_local (s : ℕ) (hB1 : 1 ≤ B) {x y : PConfig CD} {w : ISite}
    (h : ∀ z ∈ nbhdP B, x (w + z) = y (w + z)) : proposal s x w = proposal s y w := by
  classical
  -- the drivers at every base `w - j e_y`, `j < B`
  have hbase : ∀ j : ℕ, j < B → drvA x (w - jy j) = drvA y (w - jy j) ∧
      drvQ x (w - jy j) = drvQ y (w - jy j) := by
    intro j hj
    have hmem : ∀ z ∈ nbhdA ∪ nbhdQ, x (w - jy j + z) = y (w - jy j + z) := by
      intro z hz
      have hmem : z - jy j ∈ nbhdP B := by
        unfold nbhdP
        exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr
          ⟨j, Finset.mem_range.mpr hj, Finset.mem_image_of_mem (fun z => z - jy j) hz⟩)
      have := h (z - jy j) hmem
      have e : w + (z - jy j) = w - jy j + z := by abel
      rw [e] at this
      exact this
    refine ⟨drvA_congr (fun z hz => ?_), drvQ_congr (fun z hz => ?_)⟩
    · rw [hmem z (Finset.mem_union_left nbhdQ hz)]
    · rw [hmem z (Finset.mem_union_right nbhdA hz)]
  have hhelp : ∀ j : ℕ, j < B → x (w + jy j - ex + vS) = y (w + jy j - ex + vS) := by
    intro j hj
    have hmem : jy j - ex + vS ∈ nbhdP B := by
      unfold nbhdP
      exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨j, Finset.mem_range.mpr hj, rfl⟩)
    have := h (jy j - ex + vS) hmem
    have e : w + (jy j - ex + vS) = w + jy j - ex + vS := by abel
    rw [e] at this
    exact this
  have hjy0 : jy 0 = 0 := by simp [jy]
  have hB : ∀ j : Fin B, Jf x j w = Jf y j w := by
    intro j
    obtain ⟨hA, hQ⟩ := hbase j j.2
    have hf := hhelp 0 (by have := j.2; omega)
    rw [hjy0, add_zero] at hf
    unfold Jf fieldOf
    rw [hA, hQ, hf]
  have hshift : ∀ j : Fin B, Jf x j (w + jy j) = Jf y j (w + jy j) := by
    intro j
    obtain ⟨hA, hQ⟩ := hbase 0 (by have := j.2; omega)
    rw [hjy0, sub_zero] at hA hQ
    have hf := hhelp j j.2
    unfold Jf fieldOf
    rw [add_sub_cancel_right, hA, hQ, hf]
  obtain ⟨hA0, hQ0⟩ := hbase 0 (by omega)
  rw [hjy0, sub_zero] at hA0 hQ0
  have hh : hcount x w = hcount y w := by
    unfold hcount
    simp only [hshift]
  have hl : lcount x w = lcount y w := by
    unfold lcount
    simp only [hshift]
  have hP : Pin s x w ↔ Pin s y w := by
    unfold Pin
    rw [hQ0, hh, hl]
  unfold proposal
  simp only [hP, hA0, hB]

end UND.Rule
