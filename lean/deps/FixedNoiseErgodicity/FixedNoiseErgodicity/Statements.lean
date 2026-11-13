/-
Copyright (c) 2026 Seth Douglas, Nidhal Mghirbi. All rights reserved.
Formalization of: S. Douglas and N. Mghirbi, "Forgetting under noise is undecidable:
ergodicity of positive-rate cellular automata at a fixed noise rate", v1.3.0,
Zenodo DOI 10.5281/zenodo.24115709.

# Statement file

This file defines, transparently and with no proofs of substance, every object that occurs in
Corollary `cor:eight` of the paper (Theorem A on `ℤ⁸`, Section 9.6), and states that corollary as
the proposition `CorEight`; it is proved as `FNE.cor_eight : CorEight` in `Main.lean`. Every
definition carries a docstring citing the paper label it mirrors.
Fidelity choices are marked **[choice]** and are collected in `BLUEPRINT.md`, Part D.

Printed statement (cor:eight). Put `j = 3`, `k = max(2, 2j) = 6`, `q = k + 1 = 7`,
`a = 2q² + 1 = 99`, `D₀ = 50q = 350` and `ε₀ = (4D₀²)^(-a) = 490000^(-99)`. For every
`ε ∈ (0, ε₀]` and every Turing machine `M`, the noisy quorum rule `F^[6]_{R_M}` on `ℤ⁸`, with
uniform replacement at rate `ε`, is a positive-rate probabilistic cellular automaton, and it is
ergodic if and only if `M` halts. The map `M ↦ F^[6]_{R_M}` is total computable.
-/
import Mathlib.Probability.ProductMeasure
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Basic
import Mathlib.Topology.ContinuousMap.Bounded.Basic
import Mathlib.Computability.Primrec.List
import Mathlib.Computability.Partrec

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace FNE

/-! ## Section 2.1: Wang sets, blocks and the checker -/

/-- `set:def-wang`. A Wang tile: its north, east, south and west edge colours.
**[choice]** Colours are natural numbers; any countable colour set can be relabelled so. -/
@[ext] structure Tile where
  /-- north edge colour -/
  N : ℕ
  /-- east edge colour -/
  E : ℕ
  /-- south edge colour -/
  S : ℕ
  /-- west edge colour -/
  W : ℕ
deriving DecidableEq

/-- `set:def-wang`. A Wang set is a finite set of tiles. -/
abbrev WangSet := Finset Tile

/-- The plane `ℤ²` of planar sites `u`. -/
abbrev Plane := ℤ × ℤ

/-- Section 2 (opening paragraph). The box `V_r = {-r, …, r}²`. -/
def box (r : ℕ) : Finset Plane :=
  Finset.Icc (-(r : ℤ)) r ×ˢ Finset.Icc (-(r : ℤ)) r

/-- Section 2. The cells of `Λ = V_1 = {-1, 0, 1}²`, as a finite type. -/
abbrev Cell := {w : Plane // w ∈ box 1}

/-- The centre `(0,0)` of `Λ`. -/
def Cell.zero : Cell := ⟨(0, 0), by decide⟩

/-- `set:def-live`. The Moore directions `D = Λ \ {(0,0)}`. -/
def mooreDirs : Finset Plane := (box 1).erase (0, 0)

/-- `set:def-wang`, `set:def-live`. A pattern `β : Λ → R` on the 3×3 window is *legal* if
horizontally adjacent cells match east-to-west and vertically adjacent cells match north-to-south.
(The pattern takes values in `R` by its type.) -/
def IsLegalBlock {R : WangSet} (β : Cell → R) : Prop :=
  (∀ w w' : Cell, w'.1 = w.1 + (1, 0) → (β w).1.E = (β w').1.W) ∧
  (∀ w w' : Cell, w'.1 = w.1 + (0, 1) → (β w).1.N = (β w').1.S)

instance {R : WangSet} : DecidablePred (IsLegalBlock (R := R)) := fun β => by
  unfold IsLegalBlock; infer_instance

/-- `set:def-live`. The set `T_R` of legal 3×3 blocks. -/
abbrev LegalBlock (R : WangSet) := {β : Cell → R // IsLegalBlock β}

/-- `set:def-live`. A live symbol `s = (λ, b)`: a legal block and a checker bit.
**[choice]** The checker bit `b ∈ {0,1}` is a `Bool` (`false` is `0`). -/
abbrev LiveSymbol (R : WangSet) := LegalBlock R × Bool

/-- `set:def-live`. The alphabet `𝒜_R = L_R ∪ {⊥}`. -/
inductive Sym (R : WangSet) where
  /-- the bottom symbol `⊥` -/
  | bot : Sym R
  /-- a live symbol -/
  | live : LiveSymbol R → Sym R
deriving DecidableEq

namespace Sym

variable {R : WangSet}

/-- `Sym R ≃ Option (LiveSymbol R)`, used only to transfer the finiteness instance. -/
def equivOption : Sym R ≃ Option (LiveSymbol R) where
  toFun | .bot => none | .live s => some s
  invFun | none => .bot | some s => .live s
  left_inv x := by cases x <;> rfl
  right_inv x := by cases x <;> rfl

instance : Fintype (Sym R) := Fintype.ofEquiv _ equivOption.symm

instance : Inhabited (Sym R) := ⟨.bot⟩

/-- The alphabet carries the discrete topology (Section 2.3: `Ω` has the product topology). -/
instance : TopologicalSpace (Sym R) := ⊥

instance : DiscreteTopology (Sym R) := ⟨rfl⟩

/-- The alphabet carries the discrete σ-algebra. -/
instance : MeasurableSpace (Sym R) := ⊤

instance : MeasurableSingletonClass (Sym R) := ⟨fun _ => trivial⟩

instance : BorelSpace (Sym R) := ⟨borel_eq_top_of_discrete.symm⟩

end Sym

/-- `set:def-live`. The live symbol `s'` is *compatible with `s` at displacement `d`*: the bits
agree, and `λ(w) = λ'(w - d)` for every `w ∈ Λ ∩ (d + Λ)`. -/
def Compatible {R : WangSet} (s s' : LiveSymbol R) (d : Plane) : Prop :=
  s.2 = s'.2 ∧ ∀ w w' : Cell, w'.1 = w.1 - d → s.1.1 w = s'.1.1 w'

/-- `set:def-live`. The centre `ctr(s) = λ(0,0)` of a live symbol. -/
def ctr {R : WangSet} (s : LiveSymbol R) : Tile := (s.1.1 Cell.zero).1

/-- `set:def-checker`. The condition under which the planar checker keeps `x(u)`: `x(u)` is
live and, for every `d ∈ D`, `x(u+d)` is live and compatible with `x(u)` at displacement `d`. -/
def CheckerKeeps {R : WangSet} (x : Plane → Sym R) (u : Plane) : Prop :=
  ∃ s, x u = .live s ∧ ∀ d ∈ mooreDirs, ∃ s', x (u + d) = .live s' ∧ Compatible s s' d

open Classical in
/-- `set:def-checker`. The planar checker `C : 𝒜_R^{ℤ²} → 𝒜_R^{ℤ²}`. -/
def checker {R : WangSet} (x : Plane → Sym R) : Plane → Sym R :=
  fun u => if CheckerKeeps x u then x u else .bot

/-! ## Section 2.2: the quorum rule and replacement noise -/

/-- `set:def-quorum`. Sites `(u, P) ∈ ℤ² × ℤᵏ`. For `k = 6` this is `ℤ⁸`.
**[choice]** `ℤ^{2+k}` is written `ℤ² × ℤᵏ`, as in the paper's coordinates `(u, P)`. -/
abbrev Site (k : ℕ) := Plane × (Fin k → ℤ)

/-- `set:def-quorum`. Configurations `Ω = 𝒜_R^{ℤ² × ℤᵏ}`. -/
abbrev Config (k : ℕ) (R : WangSet) := Site k → Sym R

/-- `set:def-quorum`. The providers `c_0 = 0` and `c_i = e_i` (`1 ≤ i ≤ k`).
**[choice]** The index set `{0, …, k}` is `Option (Fin k)`: `none` is `0` and `some i` is
`i + 1`. -/
def provider (k : ℕ) : Option (Fin k) → (Fin k → ℤ)
  | none => 0
  | some i => Pi.single i 1

/-- `set:def-quorum`. The checked configuration `y(u, P) = C(x(·, P))(u)`: the checker run in
every plane. -/
def checkAll {k : ℕ} {R : WangSet} (x : Config k R) : Config k R :=
  fun v => checker (fun u => x (u, v.2)) v.1

/-- `set:def-quorum`. The number `#{i ∈ {0,…,k} : y(u, P + c_i) = s}` of providers reading `s`. -/
def quorumCount {k : ℕ} {R : WangSet} (y : Config k R) (v : Site k) (s : Sym R) : ℕ :=
  (Finset.univ.filter (fun i : Option (Fin k) => y (v.1, v.2 + provider k i) = s)).card

open Classical in
/-- `set:def-quorum`. The quorum rule `F^[k]_R`: `F(x)(u,P) = s` if `s` is live and at least `k`
of the `k + 1` readings `y(u, P + c_i)` equal `s`; otherwise `⊥`.
**[choice]** The live symbol is picked with `Classical.choose`; for `k ≥ 2` it is unique
(`mem:basic`(a)), so the choice is immaterial for `k = 6`. -/
def quorumRule (k : ℕ) (R : WangSet) (x : Config k R) : Config k R := fun v =>
  if h : ∃ s : LiveSymbol R, k ≤ quorumCount (checkAll x) v (.live s) then .live h.choose
  else .bot

/-- `set:def-noise`. The law of a replacement indicator `η_t(v)`: `true` (a replacement event)
with probability `ε`. -/
def flagLaw (ε : ℝ) : Measure Bool :=
  ENNReal.ofReal ε • Measure.dirac true + ENNReal.ofReal (1 - ε) • Measure.dirac false

/-- `set:def-noise`. The uniform law on the alphabet `𝒜_R`, the law of a replacement value
`ζ_t(v)`. -/
def uniformSym (R : WangSet) : Measure (Sym R) :=
  (Fintype.card (Sym R) : ℝ≥0∞)⁻¹ • Measure.count

/-- `set:def-noise`. A noise realisation: `ω (t, v) = (η_{t+1}(v), ζ_{t+1}(v))` for `t ≥ 0`.
**[choice]** Time `t + 1 ≥ 1` of the paper is index `t` here. -/
abbrev Noise (k : ℕ) (R : WangSet) := ℕ × Site k → Bool × Sym R

/-- `set:def-noise`. The law of the noise: all `η_t(v)` and `ζ_t(v)` are independent,
`P(η_t(v) = 1) = ε` and `ζ_t(v)` is uniform on `𝒜_R`. -/
def noiseLaw (k : ℕ) (R : WangSet) (ε : ℝ) : Measure (Noise k R) :=
  Measure.infinitePi (fun _ : ℕ × Site k => (flagLaw ε).prod (uniformSym R))

/-- `set:def-noise`. The process from `x` driven by the noise `ω`: `X_0 = x` and
`X_{t+1}(v) = ζ_{t+1}(v)` if `η_{t+1}(v) = 1`, and `F^[k]_R(X_t)(v)` otherwise. -/
def run {k : ℕ} {R : WangSet} (x : Config k R) (ω : Noise k R) : ℕ → Config k R
  | 0 => x
  | t + 1 => fun v => if (ω (t, v)).1 then (ω (t, v)).2 else quorumRule k R (run x ω t) v

/-- `set:def-noise`. `μΦ^t`: the law of `X_t` when `X_0` has law `μ` and is independent of the
noise. -/
def law (k : ℕ) (R : WangSet) (ε : ℝ) (μ : Measure (Config k R)) (t : ℕ) :
    Measure (Config k R) :=
  (μ.prod (noiseLaw k R ε)).map (fun p => run p.1 p.2 t)

/-- `set:def-noise`. A measure `μ` is *invariant* if `μΦ = μ`. -/
def IsInvariant (k : ℕ) (R : WangSet) (ε : ℝ) (μ : Measure (Config k R)) : Prop :=
  law k R ε μ 1 = μ

/-- `set:def-noise` (the displayed formula after it). The law of `X_{t+1}(v)` given `X_t = x`:
`(1 - ε) δ_{F(x)(v)} + ε · uniform`. -/
def siteLaw (k : ℕ) (R : WangSet) (ε : ℝ) (x : Config k R) (v : Site k) : Measure (Sym R) :=
  ENNReal.ofReal (1 - ε) • Measure.dirac (quorumRule k R x v) + ENNReal.ofReal ε • uniformSym R

/-- `set:def-noise` and the paragraph after `set:def-quorum`: the process is a probabilistic
cellular automaton with positive rates. Spelled out:
(i) the deterministic rule commutes with every translation of `ℤ² × ℤᵏ`;
(ii) it is local, with neighbourhood `𝒩 = Λ × {c_0, …, c_k}`;
(iii) given `X_0 = x`, the values `X_1(v)` are independent with laws `siteLaw x v`;
(iv) every symbol has positive probability under every `siteLaw x v` ("positive rates").
**[choice]** The paper's phrase "positive-rate probabilistic cellular automaton" is rendered by
these four clauses. -/
def IsPositiveRatePCA (k : ℕ) (R : WangSet) (ε : ℝ) : Prop :=
  (∀ (w : Site k) (x : Config k R),
      quorumRule k R (fun v => x (v + w)) = fun v => quorumRule k R x (v + w)) ∧
  (∀ (x x' : Config k R) (v : Site k),
      (∀ d ∈ box 1, ∀ i : Option (Fin k),
        x (v + (d, provider k i)) = x' (v + (d, provider k i))) →
      quorumRule k R x v = quorumRule k R x' v) ∧
  (∀ x : Config k R,
      law k R ε (Measure.dirac x) 1 = Measure.infinitePi (fun v => siteLaw k R ε x v)) ∧
  (∀ (x : Config k R) (v : Site k) (s : Sym R), 0 < siteLaw k R ε x v {s})

/-! ## Section 2.3: ergodicity -/

/-- `set:def-ergodic` (weak convergence). `μ_t → π` weakly: `∫ f dμ_t → ∫ f dπ` for every bounded
continuous `f : Ω → ℝ`. `Ω` carries the product topology of the discrete alphabet. -/
def WeakTendsto {Ω : Type*} [MeasurableSpace Ω] [TopologicalSpace Ω]
    (μs : ℕ → Measure Ω) (π : Measure Ω) : Prop :=
  ∀ f : BoundedContinuousFunction Ω ℝ,
    Tendsto (fun t => ∫ x, f x ∂(μs t)) atTop (𝓝 (∫ x, f x ∂π))

/-- `set:def-ergodic`. The process is *ergodic* if it has exactly one invariant probability
measure `π`, and `μΦ^t → π` weakly for every probability measure `μ` on `Ω`. -/
def IsErgodic (k : ℕ) (R : WangSet) (ε : ℝ) : Prop :=
  ∃ π : Measure (Config k R), IsProbabilityMeasure π ∧ IsInvariant k R ε π ∧
    (∀ π' : Measure (Config k R), IsProbabilityMeasure π' → IsInvariant k R ε π' → π' = π) ∧
    ∀ μ : Measure (Config k R), IsProbabilityMeasure μ → WeakTendsto (fun t => law k R ε μ t) π

/-! ## Turing machines (Section 6.6, paragraph "Machines") -/

/-- Head moves. -/
inductive Move where
  | left
  | stay
  | right
deriving DecidableEq

/-- The displacement of a head move. -/
def Move.toInt : Move → ℤ
  | .left => -1
  | .stay => 0
  | .right => 1

/-- Section 6.6, "Machines": a Turing machine has finitely many states, among them an initial
state and a set of halting states, a finite tape alphabet with a blank symbol, and a transition
function; it runs on a two-sided tape.
**[choice]** Finite encoding: states and tape symbols are natural numbers, the initial state is
`0` and the blank is `0`. The transition function is `table`: on state `q` reading `a`, the
first entry `((q, a), (q', a', m))` says: go to `q'`, write `a'`, move by `m`. A pair `(q, a)` with
no entry leaves the configuration unchanged (an idle self-loop). The states of the machine are
`0` and the states occurring in `table` and `halting`; its symbols are `0` and the symbols
occurring in `table`. Every machine of the paper has such an encoding. -/
structure TuringMachine where
  /-- transition table -/
  table : List ((ℕ × ℕ) × (ℕ × ℕ × Move))
  /-- halting states -/
  halting : List ℕ

/-- A configuration of a Turing machine: state, head position, two-sided tape. -/
structure TMConfig where
  /-- current state -/
  state : ℕ
  /-- head position -/
  head : ℤ
  /-- tape contents -/
  tape : ℤ → ℕ

namespace TuringMachine

/-- The start: initial state `0`, head at `0`, blank (all-`0`) two-sided tape. -/
def start : TMConfig := ⟨0, 0, fun _ => 0⟩

/-- One step of the machine. -/
def step (M : TuringMachine) (c : TMConfig) : TMConfig :=
  match M.table.lookup (c.state, c.tape c.head) with
  | some (q, a, m) => ⟨q, c.head + m.toInt, Function.update c.tape c.head a⟩
  | none => c

/-- Section 6.6: `M` *halts* if, started on a blank two-sided tape, it enters a halting state. -/
def Halts (M : TuringMachine) : Prop :=
  ∃ n : ℕ, (M.step^[n] start).state ∈ M.halting

end TuringMachine

/-! ## Encodings for computability -/

/-- `Move ≃ Fin 3`. -/
def Move.equivFin : Move ≃ Fin 3 where
  toFun | .left => 0 | .stay => 1 | .right => 2
  invFun i := if i = 0 then .left else if i = 1 then .stay else .right
  left_inv m := by cases m <;> rfl
  right_inv i := by fin_cases i <;> rfl

instance : Primcodable Move := Primcodable.ofEquiv _ Move.equivFin

/-- `TuringMachine ≃ (table, halting states)`. -/
def TuringMachine.equivProd :
    TuringMachine ≃ List ((ℕ × ℕ) × (ℕ × ℕ × Move)) × List ℕ where
  toFun M := (M.table, M.halting)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable TuringMachine := Primcodable.ofEquiv _ TuringMachine.equivProd

/-- `Tile ≃ ℕ⁴`. -/
def Tile.equivProd : Tile ≃ ℕ × ℕ × ℕ × ℕ where
  toFun t := (t.N, t.E, t.S, t.W)
  invFun p := ⟨p.1, p.2.1, p.2.2.1, p.2.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Primcodable Tile := Primcodable.ofEquiv _ Tile.equivProd

/-! ## Corollary `cor:eight` -/

/-- `cor:eight`. The rate `ε₀ = (4 D₀²)^(-a)` with `q = 7`, `D₀ = 50 q = 350` and
`a = 2 q² + 1 = 99`; numerically `490000^(-99)` (see `eps0_eq` in `Basic.lean`). -/
def eps0 : ℝ := ((4 * (50 * 7 : ℝ) ^ 2) ^ (2 * 7 ^ 2 + 1))⁻¹

/-- **Corollary `cor:eight` (Theorem A on `ℤ⁸`).** There is a total computable map `M ↦ R_M`
from Turing machines to finite Wang sets such that for every `ε ∈ (0, ε₀]` and every machine
`M`, the noisy quorum rule `F^[6]_{R_M}` on `ℤ² × ℤ⁶ = ℤ⁸` with uniform replacement at rate `ε`
is a positive-rate probabilistic cellular automaton, and it is ergodic if and only if `M` halts.

**[choice]** The family is quantified existentially (the paper's family `R_M` of `def:family`
is the intended witness; see `BLUEPRINT.md`, decision D2). A Wang set is computed as a list
of tiles (`Finset` has no `Primcodable` instance in Mathlib); the Wang set is its set of
entries. Computability of `M ↦ F^[6]_{R_M}` is rendered as computability of `M ↦ R_M`, from
which the local rule is an explicit finite construction (decision D4). -/
def CorEight : Prop :=
    ∃ Rfam : TuringMachine → List Tile, Computable Rfam ∧
      ∀ ε : ℝ, 0 < ε → ε ≤ eps0 → ∀ M : TuringMachine,
        IsPositiveRatePCA 6 (Rfam M).toFinset ε ∧
          (IsErgodic 6 (Rfam M).toFinset ε ↔ M.Halts)

end FNE
