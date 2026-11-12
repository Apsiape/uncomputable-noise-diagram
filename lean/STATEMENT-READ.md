# Statement eye-read (session 11, 11 Nov 2026)

`UncomputableNoiseDiagram/Statements.lean` (sha256 `b5c9e965b2ffbb39d2817ab4c3a41b3a71d463cbe1a0f6f186a8cc8833d0aa2c`,
unchanged since commit `4d0c30a`, session 1) read against the released v1.1.0 text of S. Douglas and
N. Mghirbi, "One noisy cellular automaton with an uncomputable noise diagram" (Zenodo DOI
10.5281/zenodo.24152233; `paper/main.tex` sha256 `0f8e5445…`, `paper/main.pdf` sha256 `c7b3fa16…`):
Theorem A (introduction, PDF p. 2, `main.tex` l. 88–91), Theorem 9.3 (`thm:main`, PDF p. 25, l. 818–821)
and Corollary 9.4 (`cor:undecidable`, PDF p. 25, l. 829–831). The PDF wording was checked against the
TeX for all three. The meaning of each clause comes from the Section 2 text (`main.tex` l. 159–164) and
the description of `U` in Section 4.1 (l. 367); these are read in the second table. Fidelity notes
F1–F14 are those of `STATUS.md` ("Statement fidelity"); all `[choice]` items were ACCEPTED by QB in
session 2. These are exactly the statements the comparator checks (`Challenge.lean`): the targets
`UND.theorem_A : UND.TheoremA`, `UND.corollary_9_4 : UND.CorollaryNineFour`,
`UND.one_rule_undecidable : UND.OneRuleUndecidable`.

**Verdict: faithful.** Every clause is rendered. The renderings that are not word-for-word are the
accepted choices F1–F14. Each is either a presentation of a finite object, an explicit form of a
quantifier, or a strengthening of the formal statement: every machine instead of one universal
machine, and rates confined to `(0, 1)`. No clause is weakened, with one exception that is an accepted
choice of form: Theorem 9.3 names the automaton (6) and the intervals (17), and the formal statement
quantifies them existentially (row T0).

## Theorem A (introduction)

Printed: "Fix a universal deterministic machine `U` whose halting set on positive unary inputs is
undecidable. **Theorem A.** There is one computably specified cellular automaton on `ℤ⁶`, with a finite
alphabet and a finite neighbourhood, and computable disjoint rational open intervals `I_n`, such that at
every rate in `I_n` uniform whole-symbol replacement makes the automaton ergodic exactly when `U(n)`
halts. Nonhalting gives at least two translation-invariant stationary laws. Halting gives a unique
stationary law attracting every initial law."

| # | Printed clause | Lean (`Statements.lean`) | Verdict |
|---|---|---|---|
| A1 | "Fix a universal deterministic machine `U` …" | `def TheoremA : Prop := ∀ U : UPD.Machine, …` | Faithful, stronger (F12): stated for every machine; the construction does not use universality. Universality appears where it is used, in Corollary 9.4 (`UPD.Universal`, row C1). |
| A2 | "… whose halting set on positive unary inputs …" (Section 4.1: "deterministic one-way-tape universal machine on positive unary inputs, with finite tape alphabet `Γ_U` containing blank and 1 … Absorbing states FAIL, HALT distinct from its working states") | `UPD.Machine` (states `Fin (numStates+1)`, initial state `0` not halting; symbols `Fin (numSymbols+2)`, blank `0`, `1`; moves left/right), `UPD.Machine.start` (cells `0 … n-1` hold `1`), `UPD.Machine.HaltsOn U n := ∃ t c, U.run n t = some c ∧ U.halting c.state = true` | Faithful (F11): finite encoding of a one-way-tape machine; a move left from cell `0` ends the run without halting (the printed machine never makes it; `P` routes tape exits to FAIL); no stay moves and a non-halting initial state (a universal machine never starts halting; stay moves compile away). Positive inputs: `1 ≤ n` in row A6. |
| A3 | "There is one … cellular automaton on `ℤ⁶`" | `∃ (A : CA 6) …`; `abbrev Site (d : ℕ) := Fin d → ℤ` | Faithful (F1: `ℤ⁶` as `Fin 6 → ℤ`; the paper's `(u, P) ∈ ℤ² × ℤ⁴` is an identification inside the proof). |
| A4 | "computably specified" | not rendered | Accepted choice (F9): for a fixed `U` the automaton is one finite object and the adjective has no formal content; the development gives it by explicit definitions (`UND.theCA U`, `Chart/TheCA.lean`); no computable family `U ↦ A_U` is claimed (QB, s2). |
| A5 | "with a finite alphabet and a finite neighbourhood" | `structure CA (d : ℕ)`: `numSymbols`, `numSymbols_pos : 0 < numSymbols`, `nbhd : Finset (Site d)`, `localRule : (nbhd → Fin numSymbols) → Fin numSymbols`; `CA.apply A x w = A.localRule (fun z => x (w + z.1))` | Faithful (F2): alphabet presented as `Fin |Σ|` (nonempty); one finite neighbourhood and one local function, translation commuting by construction. |
| A6 | "and computable disjoint rational open intervals `I_n`" | `∃ … (lo hi : ℕ → ℚ), NoiseDiagram U A lo hi`, whose first conjunct is `IsWindowFamily lo hi`: computable presentations `n ↦ (p, q)`, `q > 0`, of `lo n` and `hi n` (`Presents`); `∀ n ≥ 1, 0 < lo n ∧ lo n < hi n ∧ hi n < 1`; pairwise disjoint `window lo hi n = Set.Ioo (lo n) (hi n)` for distinct `n, m ≥ 1` | Faithful (F10): rational endpoints with computable presentations as pairs of naturals (the hard-model convention); open, nonempty, pairwise disjoint. `0 < lo`, `hi < 1` make "rates" explicit (the paper's intervals lie in `(0, ε_*)`): a stronger statement. Indexing `n ≥ 1` matches "positive unary inputs". |
| A7 | "such that at every rate in `I_n`" | `∀ n : ℕ, 1 ≤ n → ∀ ε ∈ window lo hi n, …` | Faithful. |
| A8 | "uniform whole-symbol replacement" | `CA.noiseLaw`, `CA.update`, `CA.run`, `CA.law` (second table, rows S2–S4) | Faithful (F3, F4). |
| A9 | "makes the automaton ergodic exactly when `U(n)` halts" | `(A.IsErgodic ε ↔ U.HaltsOn n)` | Faithful (F5; second table, row S6). |
| A10 | "Nonhalting gives at least two translation-invariant stationary laws." | `(¬ U.HaltsOn n → A.HasTwoTIStationaryLaws ε)`; `HasTwoTIStationaryLaws`: `∃ μ₁ μ₂, μ₁ ≠ μ₂ ∧` both probability measures, stationary and translation invariant | Faithful (F7). |
| A11 | "Halting gives a unique stationary law attracting every initial law." | `(U.HaltsOn n → A.IsErgodic ε ∧ A.PullbackEventuallySingleton ε)` | Faithful (F5): `IsErgodic` is a stationary probability `π` that is the only stationary probability, with `law ε μ t → π` weakly for every initial probability `μ`. The extra conjunct is Theorem 9.3's pullback clause (row T6). |
| A12 | (sentence after Theorem A) "In particular, the noise diagram, the set of rates at which `F_ε` is ergodic, is undecidable at rational rates for this rule (Corollary 9.4)." | `def OneRuleUndecidable : Prop := ∃ (A : CA 6) (lo hi : ℕ → ℚ), IsWindowFamily lo hi ∧ PromiseUndecidable A lo hi` | Faithful (F14): one fixed automaton on `ℤ⁶` and windows on which ergodicity at rational rates is promise-undecidable; derived from Corollary 9.4 and the existence of a universal machine (`UPD.Compiler.univMachine_universal`, reused, proved in the hard-model core; corrected 12 Nov 2026, the earlier text named `UPD.existsUniversal`, which this development does not import). |

## Theorem 9.3 (`thm:main`)

Printed: "For the single automaton (6) and the rational intervals (17), for every `n ≥ 1` and every
`ε ∈ I_n`, `F_ε` is ergodic ⟺ `U(n)` halts. If `U(n)` does not halt there are at least two
translation-invariant stationary laws. If it halts the unique stationary law attracts every initial law,
and every finite-window common-noise pullback image is almost surely eventually a singleton."

| # | Printed clause | Lean | Verdict |
|---|---|---|---|
| T0 | "For the single automaton (6) and the rational intervals (17)" | `TheoremA := ∀ U, ∃ (A : CA 6) (lo hi : ℕ → ℚ), NoiseDiagram U A lo hi` | Accepted choice of form (F9, F12): the checked statement is existential, as in Theorem A. The witnesses produced by the proof are the automaton (6) and the intervals (17): `theorem_A` unfolds through `UND.Memory.theoremA_of_halting` and `UND.theoremA_of_theCA` to `⟨UND.theCA U, UND.Param.loF, UND.Param.hiF, noiseDiagram_of_branches U (theCA U) …⟩`, with `theCA U` the automaton of (6) (Prop 2.1: `UND.prop_2_1_theCAOf`) and `loF n = 2C/ℓ_{n+n₀}`, `hiF n = 21C/(10ℓ_{n+n₀})` (17). The comparator certifies the existential form; that the witnesses are (6) and (17) is read from these definitions. |
| T1 | "for every `n ≥ 1` and every `ε ∈ I_n`" | `∀ n : ℕ, 1 ≤ n → ∀ ε ∈ window lo hi n` | Faithful. |
| T2 | "`F_ε` is ergodic ⟺ `U(n)` halts" | `(A.IsErgodic ε ↔ U.HaltsOn n)` | Faithful (F5, F11). |
| T3 | "If `U(n)` does not halt there are at least two translation-invariant stationary laws." | `(¬ U.HaltsOn n → A.HasTwoTIStationaryLaws ε)` | Faithful (F6, F7). |
| T4 | "If it halts the unique stationary law …" | `U.HaltsOn n → A.IsErgodic ε ∧ …`; `IsErgodic` contains `∃ π, IsProbabilityMeasure π ∧ A.IsStationary ε π ∧ (∀ π', IsProbabilityMeasure π' → A.IsStationary ε π' → π' = π)` | Faithful (F4, F5). |
| T5 | "… attracts every initial law" | `∀ μ, IsProbabilityMeasure μ → FNE.WeakTendsto (fun t => A.law ε μ t) π` | Faithful (F5): weak convergence = convergence of integrals of every bounded continuous real function (product topology of the discrete alphabet), the forgetting core's `FNE.WeakTendsto` (copied verbatim into the challenge). |
| T6 | "and every finite-window common-noise pullback image is almost surely eventually a singleton" | `A.PullbackEventuallySingleton ε := ∀ O : Finset (Site d), ∀ᵐ ω ∂(A.noiseLaw₂ ε), ∃ j₀, ∀ j ≥ j₀, ∀ x x', ∀ w ∈ O, A.pullback ω j x w = A.pullback ω j x' w`, with `pullback ω j x = flow ω (-j) j x` (`Ψ_{-j,0}`), two-sided noise `noiseLaw₂` on `ℤ × Site d` | Faithful, rendering choice (F8): the projection of `K_j = Ψ_{-j,0}(Σ^{ℤ⁶})` to `O` is one point for all `j ≥ j₀`. "For every `O`, a.s." equals "a.s., for every `O`" since there are countably many windows. |

## Corollary 9.4 (`cor:undecidable`)

Printed: "For this fixed automaton, deciding ergodicity at a rational noise rate is undecidable, even
under the promise that the rate lies in one of the intervals `I_n`." (Its hypothesis is the standing
"Fix a universal deterministic machine `U` whose halting set on positive unary inputs is undecidable".)

| # | Printed clause | Lean | Verdict |
|---|---|---|---|
| C1 | (standing) `U` universal: "halting set on positive unary inputs is undecidable" | `∀ U : UPD.Machine, UPD.Universal U → …`; `UPD.Universal U := ¬ ComputablePred (fun n : ℕ => 1 ≤ n ∧ U.HaltsOn n)` | Faithful (F11, F13): only undecidability of the positive-input halting set is assumed, which is what the proof uses (the hard-model core's `[choice]`, a weaker hypothesis). |
| C2 | "For this fixed automaton" | `∃ (A : CA 6) (lo hi : ℕ → ℚ), NoiseDiagram U A lo hi ∧ PromiseUndecidable A lo hi` | Faithful (F13): "this fixed automaton" is the same `A` (and the same intervals) in both conjuncts, so the automaton is the one of Theorem 9.3 (row T0 for the witnesses). |
| C3 | "deciding ergodicity at a rational noise rate … even under the promise that the rate lies in one of the intervals `I_n`" | `PromiseUndecidable A lo hi := ¬ ∃ g : ℕ × ℕ → Bool, Computable g ∧ ∀ n : ℕ, 1 ≤ n → ∀ p : ℕ × ℕ, 0 < p.2 → ((p.1 : ℝ) / p.2) ∈ window lo hi n → (g p = true ↔ A.IsErgodic ((p.1 : ℝ) / p.2))` | Faithful (F13): a rate is presented by a pair of naturals `p.1 / p.2`, `p.2 > 0` (F10); "undecidable" for the promise problem means no computable decider answers correctly on every presented rate inside some `I_n`, `n ≥ 1`; answers outside the promise are unconstrained. |

## Definitions the clauses use (Section 2, `main.tex` l. 159–164)

| # | Printed sentence | Lean | Verdict |
|---|---|---|---|
| S1 | "A cellular automaton on a finite alphabet `Σ` and lattice `ℤ^d` is a map `F` given by one finite neighbourhood `N_F` and one function `f : Σ^{N_F} → Σ`." | `structure CA`, `CA.apply` | Faithful (F2). |
| S2 | "Its uniform replacement perturbation has independent variables `E_t(w) ∼ Bernoulli(ε)` and `Z_t(w)` uniform on `Σ`, at all sites and integer times." | `CA.noiseLaw A ε := Measure.infinitePi (fun _ : ℕ × Site d => (FNE.flagLaw ε).prod A.uniformLaw)`; `FNE.flagLaw ε := ofReal ε • dirac true + ofReal (1 - ε) • dirac false` (forgetting core, verbatim in the challenge); `uniformLaw := |Σ|⁻¹ • count`; two-sided `noiseLaw₂` on `ℤ × Site d` for the pullback clause | Faithful (F3). One-sided noise for the forward process (time starts at `0`; index `t` drives the step to `t + 1`, the forgetting core's convention, F3 `[choice]`); two-sided noise for pullbacks. |
| S3 | "The update is `X_t(w) = Z_t(w)` if `E_t(w) = 1`, `F(X_{t-1})(w)` if `E_t(w) = 0`. The replacement is of the entire product symbol." | `CA.update A e x := fun w => if (e w).1 then (e w).2 else A.apply x w`; `CA.run` | Faithful: whole-symbol replacement. |
| S4 | "All coupled trajectories use these same variables. A stationary law is fixed by this Markov kernel." | `CA.law A ε μ t := (μ.prod (A.noiseLaw ε)).map (fun p => A.run p.1 p.2 t)`; `IsStationary A ε μ := A.law ε μ 1 = μ`; `flow`/`pullback` driven by one common `ω` | Faithful (F4); common noise for coupled trajectories is `flow ω`. |
| S5 | "Translation invariance means invariance under every spatial translation." | `IsTranslationInvariant A μ := ∀ a, μ.map (A.shift a) = μ`, `shift a x = fun w => x (w + a)` | Faithful (F6; all `a`, so the sign convention is immaterial). |
| S6 | "Ergodicity means a unique stationary law and weak convergence to it from every initial law." | `IsErgodic` (rows T4, T5) | Faithful (F5): "law" read as probability measure; weak convergence of laws as above. |

## Notes for QB (none changes a statement)

1. **T0** is the one place where the printed statement names concrete objects and the checked statement is
   existential (accepted in session 2 with F9 and F12). A Lean appendix should say so: the comparator
   certifies `∀ U, ∃ A lo hi, NoiseDiagram U A lo hi`; the proof's witnesses are `UND.theCA U` and the
   intervals (17) (`UND.Param.loF`, `UND.Param.hiF`), by the definitions cited in row T0.
2. The header comment of `Statements.lean` cites v1.0.0 (DOI 10.5281/zenodo.24147269). The file is
   frozen (its sha256 is recorded above and in `evidence/FROZEN-STATEMENT.json`), and Theorem A,
   Theorem 9.3 and Corollary 9.4 are printed identically in v1.1.0 (QB, s10), so the comment was left
   unchanged; the root module's docstring now cites v1.1.0.
3. The statement is stronger than printed in two places: every machine `U` (A1), and rates confined
   to `(0, 1)` (A6). Corollary 9.4 assumes only undecidability of the positive-input halting set (C1).
