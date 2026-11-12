/-
Copyright (c) 2026 Seth Douglas, Nidhal Mghirbi. All rights reserved.
Released under the Apache License 2.0.
Formalization of: S. Douglas and N. Mghirbi, "One noisy cellular automaton with an uncomputable
noise diagram", v1.0.0, Zenodo DOI 10.5281/zenodo.24147269.

# Statement file

This file defines, transparently and with no proofs of substance, every object that occurs in
Theorem 9.3 (`thm:main`, printed in Section 9; Theorem A of the introduction) and Corollary 9.4
(`cor:undecidable`), and states them as the propositions `UND.TheoremA` and
`UND.CorollaryNineFour`. Following the ruling made for the forgetting core (session 9) and used
by the hard-model core, the statement file holds the propositions; the theorems
`UND.theorem_A : UND.TheoremA` and `UND.corollary_9_4 : UND.CorollaryNineFour` live in
`Main.lean`. Every definition carries a docstring citing the paper passage it mirrors.
Fidelity choices are marked **[choice]**; each is explained in `STATUS.md` ("Statement fidelity")
and `BLUEPRINT.md`, Part D.

Reused statement-level definitions (exact matches, imported, not copied):
* from the forgetting core (`FixedNoiseErgodicity/Statements.lean`): `FNE.flagLaw` (the law of a
  replacement flag) and `FNE.WeakTendsto` (weak convergence of laws);
* from the hard-model core (`UndecidablePhaseDiagram/Statements.lean`): `UPD.Machine` (a
  deterministic one-way-tape machine on unary inputs), `UPD.Machine.HaltsOn`, `UPD.Universal`
  (undecidable halting set on positive inputs) and `UPD.ExistsUniversal`.
The forgetting core's process, law, invariance and ergodicity (`FNE.run`, `FNE.law`,
`FNE.IsInvariant`, `FNE.IsErgodic`) are hard-wired to its quorum rule `F^[k]_R` on `ℤ² × ℤᵏ`, so
they are re-defined here, in the same shape, for an arbitrary cellular automaton.

Printed statement (Theorem A). Fix a universal deterministic machine `U` whose halting set on
positive unary inputs is undecidable. There is one computably specified cellular automaton on
`ℤ⁶`, with a finite alphabet and a finite neighbourhood, and computable disjoint rational open
intervals `I_n`, such that at every rate in `I_n` uniform whole-symbol replacement makes the
automaton ergodic exactly when `U(n)` halts. Nonhalting gives at least two
translation-invariant stationary laws. Halting gives a unique stationary law attracting every
initial law.

Printed statement (Theorem 9.3). For the single automaton (6) and the rational intervals (17),
for every `n ≥ 1` and every `ε ∈ I_n`, `F_ε` is ergodic iff `U(n)` halts. If `U(n)` does
not halt there are at least two translation-invariant stationary laws. If it halts the unique
stationary law attracts every initial law, and every finite-window common-noise pullback image is
almost surely eventually a singleton.

Printed statement (Corollary 9.4). For this fixed automaton, deciding ergodicity at a rational
noise rate is undecidable, even under the promise that the rate lies in one of the intervals
`I_n`.
-/
import FixedNoiseErgodicity.Statements
import UndecidablePhaseDiagram.Statements

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal

namespace UND

/-! ## Section 2: cellular automata and uniform replacement -/

/-- Section 2, first paragraph: the lattice `ℤ^d`; a site is a map `Fin d → ℤ`.
**[choice]** `ℤ⁶` is `Fin 6 → ℤ`; the paper's coordinates `(u, P) ∈ ℤ² × ℤ⁴` are an
identification made inside the proof. -/
abbrev Site (d : ℕ) := Fin d → ℤ

/-- Section 2, first paragraph: "A cellular automaton on a finite alphabet `Σ` and lattice `ℤ^d`
is a map `F` given by one finite neighbourhood `N_F` and one function `f : Σ^{N_F} → Σ`."
**[choice]** The finite alphabet is `Fin numSymbols` with `numSymbols > 0` (every finite alphabet
is in bijection with such a type; nonemptiness makes the uniform law a probability measure). The
neighbourhood is a finite set of displacements; the local function reads the configuration on
`w + N_F`. -/
structure CA (d : ℕ) where
  /-- the size `|Σ|` of the alphabet; the symbols are `Fin numSymbols` -/
  numSymbols : ℕ
  /-- the alphabet is nonempty -/
  numSymbols_pos : 0 < numSymbols
  /-- the finite neighbourhood `N_F` -/
  nbhd : Finset (Site d)
  /-- the local function `f : Σ^{N_F} → Σ` -/
  localRule : (nbhd → Fin numSymbols) → Fin numSymbols

namespace CA

variable {d : ℕ}

/-- The alphabet `Σ` of a cellular automaton. It carries the discrete topology and the discrete
σ-algebra (Mathlib's instances on `Fin n`). -/
abbrev Sym (A : CA d) := Fin A.numSymbols

/-- Configurations `Σ^{ℤ^d}`, with the product topology and the product σ-algebra. -/
abbrev Config (A : CA d) := Site d → A.Sym

/-- Section 2: the global map `F(x)(w) = f((x(w + z))_{z ∈ N_F})`. It commutes with every
translation by construction. -/
def apply (A : CA d) (x : A.Config) : A.Config :=
  fun w => A.localRule (fun z => x (w + z.1))

/-- Section 2: the uniform law on `Σ`, the law of a replacement value `Z_t(w)`. -/
def uniformLaw (A : CA d) : Measure A.Sym :=
  (A.numSymbols : ℝ≥0∞)⁻¹ • Measure.count

/-- Section 2: a one-sided noise realisation, `ω (t, w) = (E_{t+1}(w), Z_{t+1}(w))` for `t ≥ 0`.
**[choice]** As in the forgetting core, the process starts at time `0`; the paper's time
`t + 1 ≥ 1` is index `t` here. -/
abbrev Noise (A : CA d) := ℕ × Site d → Bool × A.Sym

/-- Section 2: "independent variables `E_t(w) ∼ Bernoulli(ε)` and `Z_t(w)` uniform on `Σ`, at all
sites and integer times". The flag law is the forgetting core's `FNE.flagLaw`. -/
def noiseLaw (A : CA d) (ε : ℝ) : Measure A.Noise :=
  Measure.infinitePi (fun _ : ℕ × Site d => (FNE.flagLaw ε).prod A.uniformLaw)

/-- Section 2, the displayed update: `X_t(w) = Z_t(w)` if `E_t(w) = 1` and `F(X_{t-1})(w)` if
`E_t(w) = 0`, for one time slice `e = (E_t, Z_t)` of the noise. "The replacement is of the entire
product symbol." -/
def update (A : CA d) (e : Site d → Bool × A.Sym) (x : A.Config) : A.Config :=
  fun w => if (e w).1 then (e w).2 else A.apply x w

/-- Section 2: the process from `X_0 = x` driven by the noise `ω`. -/
def run (A : CA d) (x : A.Config) (ω : A.Noise) : ℕ → A.Config
  | 0 => x
  | t + 1 => A.update (fun w => ω (t, w)) (A.run x ω t)

/-- Section 2: `μ F_ε^t`, the law of `X_t` when `X_0` has law `μ` and is independent of the noise. -/
def law (A : CA d) (ε : ℝ) (μ : Measure A.Config) (t : ℕ) : Measure A.Config :=
  (μ.prod (A.noiseLaw ε)).map (fun p => A.run p.1 p.2 t)

/-- Section 2: "A stationary law is fixed by this Markov kernel": `μ F_ε = μ`. (The forgetting
core's `FNE.IsInvariant`, for this automaton.) -/
def IsStationary (A : CA d) (ε : ℝ) (μ : Measure A.Config) : Prop :=
  A.law ε μ 1 = μ

/-- Section 2: "Ergodicity means a unique stationary law and weak convergence to it from every
initial law." Same shape as the forgetting core's `FNE.IsErgodic`; weak convergence is
`FNE.WeakTendsto` (convergence of integrals of bounded continuous functions). -/
def IsErgodic (A : CA d) (ε : ℝ) : Prop :=
  ∃ π : Measure A.Config, IsProbabilityMeasure π ∧ A.IsStationary ε π ∧
    (∀ π' : Measure A.Config, IsProbabilityMeasure π' → A.IsStationary ε π' → π' = π) ∧
    ∀ μ : Measure A.Config, IsProbabilityMeasure μ →
      FNE.WeakTendsto (fun t => A.law ε μ t) π

/-- The spatial translate `(T_a x)(w) = x(w + a)`. -/
def shift (A : CA d) (a : Site d) (x : A.Config) : A.Config := fun w => x (w + a)

/-- Section 2: "Translation invariance means invariance under every spatial translation." -/
def IsTranslationInvariant (A : CA d) (μ : Measure A.Config) : Prop :=
  ∀ a : Site d, μ.map (A.shift a) = μ

/-- Theorem 9.3: at least two (distinct) translation-invariant stationary laws. -/
def HasTwoTIStationaryLaws (A : CA d) (ε : ℝ) : Prop :=
  ∃ μ₁ μ₂ : Measure A.Config, μ₁ ≠ μ₂ ∧
    IsProbabilityMeasure μ₁ ∧ A.IsStationary ε μ₁ ∧ A.IsTranslationInvariant μ₁ ∧
    IsProbabilityMeasure μ₂ ∧ A.IsStationary ε μ₂ ∧ A.IsTranslationInvariant μ₂

/-! ## Common-noise pullbacks (Lemma 8.5, `lem:pullback`; last clause of Theorem 9.3) -/

/-- Lemma 8.5: a two-sided noise realisation, `ω (t, w) = (E_t(w), Z_t(w))` at every integer time
`t` and site `w`. -/
abbrev Noise₂ (A : CA d) := ℤ × Site d → Bool × A.Sym

/-- The law of the two-sided noise: all flags and values independent, as in `noiseLaw`. -/
def noiseLaw₂ (A : CA d) (ε : ℝ) : Measure A.Noise₂ :=
  Measure.infinitePi (fun _ : ℤ × Site d => (FNE.flagLaw ε).prod A.uniformLaw)

/-- Lemma 8.5: `flow ω s n x` is the state at time `s + n` of the trajectory started from `x` at
time `s`, driven by the common noise `ω` (the map `Ψ_{s, s+n}`). -/
def flow (A : CA d) (ω : A.Noise₂) (s : ℤ) : ℕ → A.Config → A.Config
  | 0, x => x
  | n + 1, x => A.update (fun w => ω (s + n + 1, w)) (A.flow ω s n x)

/-- Lemma 8.5: the pullback `Ψ_{-j,0}(x)`: start from `x` at time `-j`, read at time `0`. -/
def pullback (A : CA d) (ω : A.Noise₂) (j : ℕ) (x : A.Config) : A.Config :=
  A.flow ω (-(j : ℤ)) j x

/-- Theorem 9.3, last clause: "every finite-window common-noise pullback image is almost surely
eventually a singleton". For every finite window `O`, almost surely there is `j₀` such that for
`j ≥ j₀` the projection to `O` of `K_j = Ψ_{-j,0}(Σ^{ℤ^d})` is one point. -/
def PullbackEventuallySingleton (A : CA d) (ε : ℝ) : Prop :=
  ∀ O : Finset (Site d), ∀ᵐ ω ∂(A.noiseLaw₂ ε), ∃ j₀ : ℕ, ∀ j : ℕ, j₀ ≤ j →
    ∀ x x' : A.Config, ∀ w ∈ O, A.pullback ω j x w = A.pullback ω j x' w

end CA

/-! ## The intervals (Section 6, displayed windows; Theorem 9.3) -/

/-- A positive rational `p.1 / p.2` presented by a pair of natural numbers with `p.2 > 0`.
**[choice]** As in the hard-model core (`UPD.CorollaryB`): rational endpoints "computable from
`n`" means that some computable map `n ↦ (p, q)` presents them. -/
def Presents (p : ℕ × ℕ) (r : ℚ) : Prop := 0 < p.2 ∧ ((p.1 : ℚ) / p.2) = r

/-- The open interval `I_n = (lo n, hi n)` of real rates. -/
def window (lo hi : ℕ → ℚ) (n : ℕ) : Set ℝ := Set.Ioo (lo n : ℝ) (hi n : ℝ)

/-- Theorem A: "computable disjoint rational open intervals `I_n`" (`n ≥ 1`). The endpoints have
computable presentations; every interval is a nonempty open interval of rates in `(0, 1)`; the
intervals are pairwise disjoint.
**[choice]** "Rates" is made explicit as `0 < lo n` and `hi n < 1` (true of the paper's
intervals, which lie below `ε_*`, and needed for `F_ε` to be a noise rate). -/
def IsWindowFamily (lo hi : ℕ → ℚ) : Prop :=
  (∃ f : ℕ → ℕ × ℕ, Computable f ∧ ∀ n, Presents (f n) (lo n)) ∧
  (∃ g : ℕ → ℕ × ℕ, Computable g ∧ ∀ n, Presents (g n) (hi n)) ∧
  (∀ n : ℕ, 1 ≤ n → 0 < lo n ∧ lo n < hi n ∧ hi n < 1) ∧
  (∀ n m : ℕ, 1 ≤ n → 1 ≤ m → n ≠ m → Disjoint (window lo hi n) (window lo hi m))

/-! ## Theorem 9.3 (Theorem A) and Corollary 9.4 -/

/-- The clauses of Theorem 9.3 for a machine `U`, an automaton `A` on `ℤ⁶` and intervals
`I_n = (lo n, hi n)`: the intervals are as in `IsWindowFamily`, and for every `n ≥ 1` and every
`ε ∈ I_n`: `F_ε` is ergodic iff `U(n)` halts; if `U(n)` does not halt there are at least two
translation-invariant stationary laws; if it halts, `F_ε` has a unique stationary law attracting
every initial law (ergodicity) and every finite-window pullback image is almost surely eventually
a singleton. -/
def NoiseDiagram (U : UPD.Machine) (A : CA 6) (lo hi : ℕ → ℚ) : Prop :=
  IsWindowFamily lo hi ∧
  ∀ n : ℕ, 1 ≤ n → ∀ ε ∈ window lo hi n,
    (A.IsErgodic ε ↔ U.HaltsOn n) ∧
    (¬ U.HaltsOn n → A.HasTwoTIStationaryLaws ε) ∧
    (U.HaltsOn n → A.IsErgodic ε ∧ A.PullbackEventuallySingleton ε)

/-- **Theorem A / Theorem 9.3.** For the machine `U` there are one cellular automaton on `ℤ⁶` with
a finite alphabet and a finite neighbourhood, and computable pairwise disjoint rational open
intervals `I_n`, with the clauses of `NoiseDiagram`.
**[choice]** Stated for every machine `U` (the construction does not use universality; as in
`UPD.TheoremA`). "Computably specified" has no formal content for one finite object and is not
rendered: the development gives the automaton by explicit definitions (see `STATUS.md`,
"Statement fidelity", item F9). -/
def TheoremA : Prop :=
  ∀ U : UPD.Machine, ∃ (A : CA 6) (lo hi : ℕ → ℚ), NoiseDiagram U A lo hi

/-- Corollary 9.4: no algorithm decides ergodicity at the rational rates of the intervals.
**[choice]** A rate is presented by a pair `p` of natural numbers (`p.1 / p.2`, `p.2 > 0`, as in
`Presents`); the promise problem is undecidable: no computable `g` answers correctly on every
presentation of a rate in some `I_n`, `n ≥ 1`. -/
def PromiseUndecidable (A : CA 6) (lo hi : ℕ → ℚ) : Prop :=
  ¬ ∃ g : ℕ × ℕ → Bool, Computable g ∧
    ∀ n : ℕ, 1 ≤ n → ∀ p : ℕ × ℕ, 0 < p.2 → ((p.1 : ℝ) / p.2) ∈ window lo hi n →
      (g p = true ↔ A.IsErgodic ((p.1 : ℝ) / p.2))

/-- **Corollary 9.4.** For a universal machine `U` (halting set on positive inputs undecidable),
the automaton and intervals of Theorem 9.3 can be chosen so that, for this fixed automaton,
ergodicity at rational rates is undecidable even under the promise that the rate lies in one of
the `I_n`. ("This fixed automaton" is rendered by stating both conclusions for the same `A`.) -/
def CorollaryNineFour : Prop :=
  ∀ U : UPD.Machine, UPD.Universal U →
    ∃ (A : CA 6) (lo hi : ℕ → ℚ), NoiseDiagram U A lo hi ∧ PromiseUndecidable A lo hi

/-- The sentence after Theorem A ("the noise diagram ... is undecidable at rational rates for this
rule") with a universal machine supplied: one fixed automaton on `ℤ⁶` whose ergodicity at the
rational rates of computable disjoint windows is undecidable. Follows from `CorollaryNineFour`
and `UPD.ExistsUniversal`. -/
def OneRuleUndecidable : Prop :=
  ∃ (A : CA 6) (lo hi : ℕ → ℚ), IsWindowFamily lo hi ∧ PromiseUndecidable A lo hi

end UND
