/-
# Section 3.3: local routing rules and the finite alphabet `R` (S7)

Node S7 of `BLUEPRINT.md` (Part A.3). ADAPTED: the shapes of the hard-model core's (O1)–(E3),
(K1)–(K3), (C0) (`UPD.SiteVal.O1 … K3, C0`, `UndecidablePhaseDiagram/Statements.lean`, Section 4),
with the decorated quarters of `Decorated.lean`, the tableau (10) in place of (C1)–(C9), and the
higher-block phase extension of `PhaseTable.lean`; NEW content.

Paper (Section 3.3): "Retain the orientation/event fields of [DMhard, Section 4, (O1)–(E3)]. … At
each side there is an orientation pair: entries in `{L, R}` on horizontal edges, in `{B, T}` on
vertical edges. There is also an event tag in `{cell, wall}² ∪ {*}`. Matching edges identify the
entire tags. … If `VW = -`, the west and east orientation pairs agree. At a wall of side `a`, the
plus entry on its west edge and minus entry on its east edge both equal `a`. Apply the transposed
rule vertically. An event tag is a pair precisely when its orientation is `(L, R)` horizontally or
`(B, T)` vertically, and is `*` otherwise. A site is a horizontal carrier when `VW = -` and the
west orientation is `(L, R)`; define vertical carriers by transposition. An active site is both.
… (E2)/(E3). On carriers introduce horizontal logical colours in `{∘} ∪ S_P` and vertical ones in
`{∘} ∪ S_P²` … Nonhorizontal carriers have empty horizontal colours; horizontal-only sites copy
those colours. Impose the transposed vertical conditions. Records are empty off active sites; at
active sites they are genuine triples `(t_S, t_C, t_N)` with `t_C ∈ S_P`, `t_S, t_N ∈ S_P ∪ {⊥}`.
Define the four flags … Require `ℓ^X = ∘` exactly when `f_X = 1`, for every side `X`. The
remaining constraints are (10) … The read-only input tracks in `t_C` agree with the local
`H_row, χ₂`. This retains precisely (K1)–(K3), the boundary rule (C0), and the displayed replacement
for (C5). The finite alphabet `R` is the set of tuples passing these tests, followed by the phase
extension above."

Formalization (generic in the machine-content alphabet, D24: `ContentOps S` gives `init`, `f_P`,
the HALT mark and the read-only tracks; the machine `P` of Section 4 supplies them in
`Chart/TheCA.lean`):
* `RVal S` (a decorated quarter, orientation pairs, event tags, logical colours, record), its
  predicates (`VW`, `HW`, carriers, flags), the tests `O1 … K3`, `C0`, the tableau `Tab` (10),
  `Allowed`, and its Wang colours `cE, cW, cN, cS`;
* the phase extension: a tile of `R` is an allowed tuple with its central word of radius `ρ_{2k}`
  (centre = its quarter; `TileOK`); tiles match when their routing colours match, their words
  overlap consistently, and the decoded phase copies horizontally and increases by one vertically
  (`TileE`, `TileN`);
* **`chartData C k : ChartData (4^k) (RTile C k)`**: the tile set with the controller's tile
  functions `Orig`, `End` (on the central quarter), `H_row` (the row bit) and `p` (the decoded
  phase).
-/
import UncomputableNoiseDiagram.Chart.Decorated
import UncomputableNoiseDiagram.Chart.PhaseTable
import UncomputableNoiseDiagram.Rule.Proposal
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 2000000

noncomputable section

namespace UND.Chart

open UPD UPD.Scaffold

/-- The machine-content data read by the tableau (10) (D24): `init(H_row, χ₂, f_S)`, the ordered
local rule `f_P`, the HALT mark, and the read-only input tracks `h_in`, `π`. -/
structure ContentOps (S : Type) where
  /-- `init(H_row, χ₂, f_S)` -/
  init : Bool → Bool → Bool → S
  /-- the ordered local rule `f_P(t_S, t_C, t_N)` -/
  fP : Option S → S → Option S → S
  /-- the content carries HALT -/
  halts : S → Bool
  /-- the read-only track `h_in` -/
  hin : S → Bool
  /-- the read-only track `π` -/
  piBit : S → Bool

/-- A routing tuple before the tests: the decorated quarter, the orientation pairs, the event tags
(`none` is `*`), the logical colours (`none` is `∘`) and the record (`none` is the empty record;
in a triple `none` is `⊥`). -/
structure RVal (S : Type) where
  /-- the decorated quarter -/
  q : DQuarter
  /-- orientation pair on the west edge -/
  oW : LR × LR
  /-- orientation pair on the east edge -/
  oE : LR × LR
  /-- orientation pair on the south edge -/
  oS : BT × BT
  /-- orientation pair on the north edge -/
  oN : BT × BT
  /-- event tag `e^W` -/
  eW : Option (Ev × Ev)
  /-- event tag `e^E` -/
  eE : Option (Ev × Ev)
  /-- event tag `e^S` -/
  eS : Option (Ev × Ev)
  /-- event tag `e^N` -/
  eN : Option (Ev × Ev)
  /-- horizontal logical colour `ℓ^W ∈ {∘} ∪ S_P` -/
  lW : Option S
  /-- horizontal logical colour `ℓ^E` -/
  lE : Option S
  /-- vertical logical colour `ℓ^S ∈ {∘} ∪ S_P²` -/
  lS : Option (S × S)
  /-- vertical logical colour `ℓ^N` -/
  lN : Option (S × S)
  /-- the record `(t_S, t_C, t_N)` -/
  k : Option (Option S × S × Option S)
  deriving DecidableEq

/-- `RVal S` is the product of its fields (used for the finiteness instance). -/
def RVal.equivProd (S : Type) : RVal S ≃
    DQuarter × (LR × LR) × (LR × LR) × (BT × BT) × (BT × BT) ×
      Option (Ev × Ev) × Option (Ev × Ev) × Option (Ev × Ev) × Option (Ev × Ev) ×
      Option S × Option S × Option (S × S) × Option (S × S) × Option (Option S × S × Option S) where
  toFun s := (s.q, s.oW, s.oE, s.oS, s.oN, s.eW, s.eE, s.eS, s.eN, s.lW, s.lE, s.lS, s.lN, s.k)
  invFun := fun ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩ =>
    ⟨a1, a2, a3, a4, a5, a6, a7, a8, a9, a10, a11, a12, a13, a14⟩
  left_inv _ := rfl
  right_inv := fun ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, _⟩ => rfl

instance (S : Type) [Fintype S] : Fintype (RVal S) := Fintype.ofEquiv _ (RVal.equivProd S).symm

namespace RVal

variable {S : Type} (s : RVal S)

/-- The vertical wall predicate of the quarter. -/
def VW : Option LR := s.q.toQ.VW

/-- The horizontal wall predicate of the quarter. -/
def HW : Option BT := s.q.toQ.HW

/-- A horizontal carrier: `VW = -` and the west orientation is `(L, R)`. -/
def IsHCarrier : Prop := s.VW = none ∧ s.oW = (.L, .R)

/-- A vertical carrier: `HW = -` and the south orientation is `(B, T)`. -/
def IsVCarrier : Prop := s.HW = none ∧ s.oS = (.B, .T)

/-- An active site is both. -/
def IsActive : Prop := s.IsHCarrier ∧ s.IsVCarrier

/-- A horizontal-only site. -/
def IsHorizontal : Prop := s.IsHCarrier ∧ ¬ s.IsVCarrier

/-- A vertical-only site. -/
def IsVertical : Prop := s.IsVCarrier ∧ ¬ s.IsHCarrier

/-- `f_W = [e^W_- = wall]` (read as `0` when `e^W = *`). -/
def fW : Bool :=
  match s.eW with
  | some (a, _) => decide (a = .wall)
  | none => false

/-- `f_E = [e^E_+ = wall]`. -/
def fE : Bool :=
  match s.eE with
  | some (_, b) => decide (b = .wall)
  | none => false

/-- `f_S = [e^S_- = wall]`. -/
def fS : Bool :=
  match s.eS with
  | some (a, _) => decide (a = .wall)
  | none => false

/-- `f_N = [e^N_+ = wall]`. -/
def fN : Bool :=
  match s.eN with
  | some (_, b) => decide (b = .wall)
  | none => false

/-- (O1): if `VW = -` the west and east pairs agree; at a wall of side `a` the plus entry of the
west pair and the minus entry of the east pair are `a`. -/
def O1 : Prop :=
  (s.VW = none → s.oW = s.oE) ∧
  (s.VW = some .L → s.oW.2 = .L ∧ s.oE.1 = .L) ∧
  (s.VW = some .R → s.oW.2 = .R ∧ s.oE.1 = .R)

/-- (O2): the transposed rule. -/
def O2 : Prop :=
  (s.HW = none → s.oS = s.oN) ∧
  (s.HW = some .B → s.oS.2 = .B ∧ s.oN.1 = .B) ∧
  (s.HW = some .T → s.oS.2 = .T ∧ s.oN.1 = .T)

/-- (E1): an event tag is a pair precisely when its orientation is `(L, R)` (horizontally) or
`(B, T)` (vertically). -/
def E1 : Prop :=
  (s.eW = none ↔ s.oW ≠ (.L, .R)) ∧ (s.eE = none ↔ s.oE ≠ (.L, .R)) ∧
  (s.eS = none ↔ s.oS ≠ (.B, .T)) ∧ (s.eN = none ↔ s.oN ≠ (.B, .T))

/-- (E2): horizontal-only sites copy both entries; active sites put `cell` in the west plus and
east minus entries; an inward-facing left wall puts `wall` in the east minus entry, an
inward-facing right wall in the west plus entry. -/
def E2 : Prop :=
  (s.IsHorizontal → s.eW = s.eE) ∧
  (s.IsActive → Ev.SecondIs s.eW .cell ∧ Ev.FirstIs s.eE .cell) ∧
  (s.VW = some .L ∧ s.oE = (.L, .R) → Ev.FirstIs s.eE .wall) ∧
  (s.VW = some .R ∧ s.oW = (.L, .R) → Ev.SecondIs s.eW .wall)

/-- (E3): the transposed rule. -/
def E3 : Prop :=
  (s.IsVertical → s.eS = s.eN) ∧
  (s.IsActive → Ev.SecondIs s.eS .cell ∧ Ev.FirstIs s.eN .cell) ∧
  (s.HW = some .B ∧ s.oN = (.B, .T) → Ev.FirstIs s.eN .wall) ∧
  (s.HW = some .T ∧ s.oS = (.B, .T) → Ev.SecondIs s.eS .wall)

/-- (K1): sites that are not horizontal carriers have empty horizontal colours; horizontal-only
sites copy them. -/
def K1 : Prop :=
  (¬ s.IsHCarrier → s.lW = none ∧ s.lE = none) ∧ (s.IsHorizontal → s.lW = s.lE)

/-- (K2): the transposed rule. -/
def K2 : Prop :=
  (¬ s.IsVCarrier → s.lS = none ∧ s.lN = none) ∧ (s.IsVertical → s.lS = s.lN)

/-- (C0): `ℓ^X = ∘` exactly when `f_X = 1`. -/
def C0 : Prop :=
  (s.lW = none ↔ s.fW = true) ∧ (s.lE = none ↔ s.fE = true) ∧
  (s.lS = none ↔ s.fS = true) ∧ (s.lN = none ↔ s.fN = true)

/-- **The tableau (10)** for the record `(t_S, t_C, t_N)`, with the read-only input tracks of
`t_C` equal to the local `H_row`, `χ₂`. -/
def Tab {S : Type} (s : RVal S) (C : ContentOps S) (tS : Option S) (tC : S) (tN : Option S) :
    Prop :=
  (s.fS = true → tS = none) ∧ (s.fS = false → ∃ x, tS = some x ∧ s.lS = some (x, tC)) ∧
  (s.fN = true → tN = none) ∧ (s.fN = false → ∃ x, tN = some x ∧ s.lN = some (tC, x)) ∧
  (s.fW = true → tC = C.init s.q.H s.q.parent.1.a.1.b2 s.fS) ∧
  (s.fW = false → s.lW = some tC) ∧
  (s.fE = false → s.lE = some (C.fP tS tC tN)) ∧
  C.halts tC = false ∧ C.hin tC = s.q.H ∧ C.piBit tC = s.q.parent.1.a.1.b2

/-- (K3): records are empty off active sites; at active sites they are triples obeying (C0) and
the tableau (10). -/
def K3 {S : Type} (s : RVal S) (C : ContentOps S) : Prop :=
  (¬ s.IsActive → s.k = none) ∧
  (s.IsActive → ∃ tS tC tN, s.k = some (tS, tC, tN) ∧ s.C0 ∧ s.Tab C tS tC tN)

/-- The tuple tests of Section 3.3. -/
def Allowed {S : Type} (s : RVal S) (C : ContentOps S) : Prop :=
  s.O1 ∧ s.O2 ∧ s.E1 ∧ s.E2 ∧ s.E3 ∧ s.K1 ∧ s.K2 ∧ s.K3 C

/-- East edge colour: the quarter colour, the orientation pair, the event tag, the logical
colour. -/
def cE : DColH × (LR × LR) × Option (Ev × Ev) × Option S := (s.q.colE, s.oE, s.eE, s.lE)

/-- West edge colour. -/
def cW : DColH × (LR × LR) × Option (Ev × Ev) × Option S := (s.q.colW, s.oW, s.eW, s.lW)

/-- North edge colour. -/
def cN : DColV × (BT × BT) × Option (Ev × Ev) × Option (S × S) := (s.q.colN, s.oN, s.eN, s.lN)

/-- South edge colour. -/
def cS : DColV × (BT × BT) × Option (Ev × Ev) × Option (S × S) := (s.q.colS, s.oS, s.eS, s.lS)

/-- Horizontal matching of routing tuples (`b` east of `a`). -/
def MatchE {S : Type} (a b : RVal S) : Prop := a.cE = b.cW

/-- Vertical matching of routing tuples (`b` north of `a`). -/
def MatchN {S : Type} (a b : RVal S) : Prop := a.cN = b.cS

end RVal

/-- The centre `(0, 0)` of the box `[-ρ, ρ]²`. -/
def boxCtr (ρ : ℕ) : ↥(FNE.box ρ) := ⟨(0, 0), by simp [FNE.box]⟩

variable {S : Type} [Fintype S] [DecidableEq S]

/-- The tests of `R` with the phase extension: an allowed tuple and its central word of radius
`ρ_{2k}`, whose centre is the tuple's quarter. -/
def TileOK (C : ContentOps S) (k : ℕ) (t : RVal S × Word (winRad k)) : Prop :=
  t.1.Allowed C ∧ t.2 (boxCtr _) = t.1.q.toQ

/-- **The finite alphabet `R`** (for the content data `C` and `B = 4^k`). -/
abbrev RTile (C : ContentOps S) (k : ℕ) := {t : RVal S × Word (winRad k) // TileOK C k t}

instance (C : ContentOps S) (k : ℕ) : Fintype (RTile C k) := Fintype.ofFinite _

/-- Horizontal matching in `R` (`b` east of `a`): the routing colours match, the central words
overlap consistently, and the decoded phase is copied. -/
def TileE (C : ContentOps S) (k : ℕ) (a b : RTile C k) : Prop :=
  RVal.MatchE a.1.1 b.1.1 ∧
  (∀ x y : ↥(FNE.box (winRad k)), x.1 = y.1 + (1, 0) → a.1.2 x = b.1.2 y) ∧
  phaseTable k b.1.2 = phaseTable k a.1.2

/-- Vertical matching in `R` (`b` north of `a`): the routing colours match, the central words
overlap consistently, and the decoded phase increases by one. -/
def TileN (C : ContentOps S) (k : ℕ) (a b : RTile C k) : Prop :=
  RVal.MatchN a.1.1 b.1.1 ∧
  (∀ x y : ↥(FNE.box (winRad k)), x.1 = y.1 + (0, 1) → a.1.2 x = b.1.2 y) ∧
  phaseTable k b.1.2 = phaseTable k a.1.2 + 1

/-- **The chart data of `R`**: the tile set with its matching relations, and the controller's
tile functions read on the central tile: `Orig`, `End` (of the quarter), the row flag `H_row`,
and the decoded lane phase `p ∈ ℤ/Bℤ`, `B = 4^k`. -/
def chartData (C : ContentOps S) (k : ℕ) : UND.Rule.ChartData (4 ^ k) (RTile C k) where
  E := TileE C k
  N := TileN C k
  orig t := decide (IsOrig t.1.1.q.toQ)
  endP t := decide (IsEnd t.1.1.q.toQ)
  hrow t := t.1.1.q.H
  phase t := phaseTable k t.1.2

end UND.Chart
