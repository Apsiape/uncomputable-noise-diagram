/-
# Section 4.1: the direct finite machine `P` and its content alphabet `S_P` (M1)

Node M1 of `BLUEPRINT.md` (Part A.4), NEW (shape of the hard-model core's `UPD.programM`,
`deltaM`, `fM`, `initM`; `UndecidablePhaseDiagram/Statements.lean`, App. C).

Paper (Section 4.1): "The machine `P` has read-only bits `h_in, π, z`, writable bits `p_*, e_*`, a
writable track `n_* ∈ {0,1,2}` and a writable track `u_* ∈ Γ_U`. Initially `h_in = H_row`,
`π = χ₂`, `z = [j = 0]`, the work tracks are zero or blank, and the sole head is at cell zero in
SCAN. A transition preserves every track not explicitly written. All unspecified cases and every
attempted tape exit go to absorbing FAIL. Right means increasing logical tape index `j` (north).
… A return to the origin with continuation `Z` means state `RET_Z`, moving left while `z = 0` and
staying with state `Z` at `z = 1`." Clauses 1–6 (SCAN, PLUS, SETEND; `R_{bc}`; APPENDN;
`SKIP_c`; FINDN, APPENDU; `RUN_q`, HALT, FAIL) are the arms of `program` below. "Let `S_P` be the
resulting finite alphabet of tape symbols with one state or a no-head mark. Define `f_P(a,b,c)` by
this ordered rule: if `b` carries a head, perform its transition, retaining a failing head if the
move points to a `⊥` neighbour (a tape end); otherwise retain its new head for a stay move or drop
it for a move. If `b` has no head but `a` moves a head north, retain `b`'s symbol and install that
new head state. Otherwise do the same for a head from `c` moving south. In the remaining case
preserve `b` without a head."

Formalization (D13: `n₀` is a variable; the selected `n₀` of Section 9 is plugged in at the end):
* `Tape U` (the tracks), `Cont` (the continuations of returns), `PState U n0`, `program`
  (`none` = unspecified), `deltaP` (unspecified cases fail without writing or moving);
* `Cell U n0 = S_P` (tape symbol with a state or the no-head mark `none`), `fromBelow`,
  `fromAbove`, **`fP`** (the ordered local rule), `initP` (`init(H_row, χ₂, f_S)`),
  `CarriesHalt`.
The direction convention is `UPD.Mv`: `up` is north (right on the logical tape), `down` south.
-/
import UncomputableNoiseDiagram.Statements
import Mathlib.Data.Fintype.Sigma
import Mathlib.Data.Fintype.Sum
import Mathlib.Data.Fintype.Option
import Mathlib.Tactic.DeriveFintype

set_option autoImplicit false
set_option synthInstance.maxSize 100000
set_option synthInstance.maxHeartbeats 2000000

namespace UND.MachineP

open UPD

variable (U : Machine) (n0 : ℕ)

/-- The tracks of a tape symbol of `P`: read-only `h_in, π, z`, writable `p_*, e_*`,
`n_* ∈ {0,1,2}`, `u_* ∈ Γ_U`. -/
structure Tape where
  /-- read-only `h_in` -/
  hin : Bool
  /-- read-only parity bit `π` -/
  pi : Bool
  /-- read-only origin mark `z` -/
  z : Bool
  /-- marks `p_*` -/
  p : Bool
  /-- end mark `e_*` -/
  e : Bool
  /-- tokens `n_* ∈ {0,1,2}` -/
  n : Fin 3
  /-- the tape `u_*` of `U` (blank `0`) -/
  u : U.Symbol
  deriving DecidableEq, Fintype

/-- The continuations of a return to the origin: `R_00`, `SKIP_0`, APPENDN, FINDN, APPENDU,
`RUN_{q_{U,0}}`. -/
inductive Cont where
  | r00
  | skip0
  | appendN
  | findN
  | appendU
  | run0
  deriving DecidableEq

instance : Fintype Cont :=
  ⟨{.r00, .skip0, .appendN, .findN, .appendU, .run0}, fun x => by cases x <;> simp⟩

/-- The states of `P`. -/
inductive PState where
  | scan
  | plus
  | setend
  /-- `RET_Z` -/
  | ret (c : Cont)
  /-- `R_{bc}`, `b ∈ {0,1}`, `c ∈ {0,1,2}` -/
  | r (b : Bool) (c : Fin 3)
  | appendN
  /-- `SKIP_c`, `0 ≤ c ≤ n₀ + 1` -/
  | skip (c : Fin (n0 + 2))
  | findN
  | appendU
  /-- `RUN_q` for a state `q` of `U` -/
  | run (q : U.State)
  | halt
  | fail
  deriving DecidableEq, Fintype

variable {U n0}

/-- The state a continuation stands for. -/
def Cont.state : Cont → PState U n0
  | .r00 => .r false 0
  | .skip0 => .skip 0
  | .appendN => .appendN
  | .findN => .findN
  | .appendU => .appendU
  | .run0 => .run 0

variable (U n0)

/-- The program of `P` (clauses 1–6 of Section 4.1); `none` is an unspecified case. -/
def program : PState U n0 → Tape U → Option (PState U n0 × Tape U × Mv)
  | .scan, g =>
    if g.hin then some (.scan, { g with p := true }, .up)
    else if g.pi then some (.plus, { g with p := true }, .up)
    else none
  | .plus, g => some (.setend, { g with p := true }, .up)
  | .setend, g => some (.ret .r00, { g with e := true }, .down)
  | .ret c, g => if g.z then some (c.state, g, .stay) else some (.ret c, g, .down)
  | .r b c, g =>
    if g.e = false then
      (if g.p = false then some (.r b c, g, .up)
       else some (.r (!b) ⟨min (c.val + 1) 2, by omega⟩, { g with p := !b }, .up))
    else
      (if c.val = 0 then none
       else if c.val = 1 then some (.ret .skip0, g, .stay)
       else if b then none
       else some (.ret .appendN, g, .stay))
  | .appendN, g =>
    if g.n = 1 then some (.appendN, g, .up)
    else if g.n = 0 then some (.ret .r00, { g with n := 1 }, .stay)
    else none
  | .skip c, g =>
    if g.n = 1 then
      (if h : c.val < n0 + 1 then some (.skip ⟨c.val + 1, by omega⟩, { g with n := 2 }, .up)
       else some (.ret .findN, g, .stay))
    else none
  | .findN, g =>
    if g.n = 2 then some (.findN, g, .up)
    else if g.n = 1 then some (.ret .appendU, { g with n := 2 }, .stay)
    else some (.ret .run0, g, .stay)
  | .appendU, g =>
    if g.u = 1 then some (.appendU, g, .up)
    else if g.u = 0 then some (.ret .findN, { g with u := 1 }, .stay)
    else none
  | .run q, g =>
    if U.halting q then some (.halt, g, .stay)
    else
      some ((if U.halting (U.trans q g.u).1 then .halt else .run (U.trans q g.u).1),
        { g with u := (U.trans q g.u).2.1 }, if (U.trans q g.u).2.2 then .up else .down)
  | .halt, g => some (.halt, g, .stay)
  | .fail, g => some (.fail, g, .stay)

/-- The step of `P`: the program; every unspecified case enters FAIL without writing or moving.
(Attempted tape exits are handled by `fP`.) -/
def deltaP (q : PState U n0) (g : Tape U) : PState U n0 × Tape U × Mv :=
  match program U n0 q g with
  | none => (.fail, g, .stay)
  | some r => r

/-- `S_P`: a tape symbol with one state or the no-head mark (`none`). -/
abbrev Cell := Tape U × Option (PState U n0)

/-- The state brought by a head that moves north from the cell `a` below, if any. -/
def fromBelow (a : Option (Cell U n0)) : Option (PState U n0) :=
  match a with
  | some (ga, some qa) => if (deltaP U n0 qa ga).2.2 = .up then some (deltaP U n0 qa ga).1 else none
  | _ => none

/-- The state brought by a head that moves south from the cell `c` above, if any. -/
def fromAbove (c : Option (Cell U n0)) : Option (PState U n0) :=
  match c with
  | some (gc, some qc) =>
    if (deltaP U n0 qc gc).2.2 = .down then some (deltaP U n0 qc gc).1 else none
  | _ => none

/-- **The ordered local rule `f_P(a, b, c)`** (`a` below, `c` above; `none` is `⊥`, a tape end):
(1) if `b` carries a head, perform its transition, retaining a failing head if the move points to a
`⊥` neighbour, otherwise retaining the new head for a stay move and dropping it for a move; (2) if
`b` has no head but `a` moves a head north, retain `b`'s symbol and install that head; (3)
otherwise the same for a head from `c` moving south; (4) otherwise preserve `b` without a head. -/
def fP (a : Option (Cell U n0)) (b : Cell U n0) (c : Option (Cell U n0)) : Cell U n0 :=
  match b.2 with
  | some qb =>
    let r := deltaP U n0 qb b.1
    if (r.2.2 = .up ∧ c = none) ∨ (r.2.2 = .down ∧ a = none) then (r.2.1, some .fail)
    else if r.2.2 = .stay then (r.2.1, some r.1)
    else (r.2.1, none)
  | none =>
    match fromBelow U n0 a with
    | some q' => (b.1, some q')
    | none =>
      match fromAbove U n0 c with
      | some q' => (b.1, some q')
      | none => (b.1, none)

/-- The initial content `init(H_row, χ₂, f_S)`: `h_in = H_row`, `π = χ₂`, `z = f_S = [j = 0]`, the
work tracks zero or blank, and the head in SCAN exactly at cell zero. -/
def initP (h pi z : Bool) : Cell U n0 :=
  (⟨h, pi, z, false, false, 0, 0⟩, if z then some .scan else none)

/-- The content carries HALT. -/
def CarriesHalt (s : Cell U n0) : Bool := decide (s.2 = some .halt)

end UND.MachineP
