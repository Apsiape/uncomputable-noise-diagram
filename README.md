# One noisy cellular automaton with an uncomputable noise diagram

Seth Douglas and Nidhal Mghirbi. Version 1.3.0, November 2026. DOI for all versions: [10.5281/zenodo.24147268](https://doi.org/10.5281/zenodo.24147268); version 1.3.0: [10.5281/zenodo.24178271](https://doi.org/10.5281/zenodo.24178271); version 1.2.0: [10.5281/zenodo.24174445](https://doi.org/10.5281/zenodo.24174445); version 1.1.0: [10.5281/zenodo.24152233](https://doi.org/10.5281/zenodo.24152233); version 1.0.0: [10.5281/zenodo.24147269](https://doi.org/10.5281/zenodo.24147269).

**This is a preprint. It has not been peer reviewed.**

## Abstract

Can varying only the noise rate of one cellular automaton encode halting? We construct one computably specified finite-alphabet, finite-range automaton on Z^4 with computable disjoint rational open rate windows. Throughout the nth window, uniform whole-symbol replacement is ergodic exactly when a fixed universal machine halts on n. Halting gives exponential coalescence simultaneously over all initial configurations and attraction from every initial law; nonhalting gives two laws invariant under every spatial translation. Planar rulers and computation boards select the input; three transverse quorum boxes, marked-parent density and interval sensors control errors. The space-time construction gives one fixed translation-invariant finite-range {0,1}-energy interaction on Z^5 with computable rational inverse-temperature windows: halting is equivalent to uniqueness among all Gibbs measures and also gives exponential weak spatial mixing in arbitrary volumes. The earlier Z^6 and Z^7 constructions, their extremal and field-response results, and the Lean verification of Theorem A and its stated corollaries are retained. The Z^4 theorem and Z^5 corollary are not formalized.

## What the paper proves

Fix a universal machine U whose halting set is undecidable. Theorem numbers refer to `paper/main.pdf`.

The main theorem:

- **Theorem A (Theorem 9.3).** One computably specified cellular automaton on Z^6, with a finite alphabet and a finite neighbourhood, and computable pairwise disjoint open intervals I_n with rational endpoints, such that at every rate in I_n uniform whole-symbol replacement makes the automaton ergodic exactly when U(n) halts. Nonhalting gives at least two translation-invariant stationary laws. Halting gives a unique stationary law attracting every initial law.
- **Corollary 9.4.** For this fixed automaton, deciding ergodicity at a rational noise rate is undecidable, even under the promise that the rate lies in one of the intervals I_n.

Halting and nonhalting windows in more detail:

- **Theorem 9.5 (exponential all-input coalescence).** If U(n) halts, then uniformly for every rate in I_n, the probability that the symbol at the origin at time t still depends on the initial configuration, when all initial configurations are run with one shared realization of the noise, is at most C_n e^(-c_n t). The rate c_n is computable from n, and C_n is computed by a procedure that terminates on every halting input. The proof is in Appendix A (Lemmas A.1-A.5).
- **Theorem 9.6 (continuum many extremal states).** If U(n) does not halt, then at every rate in I_n the set of all stationary laws has continuum many extreme points, and the corresponding normalized space-time interaction, the Gibbs model of Corollary B, has continuum many extremal Gibbs measures. These extremes are not asserted to be translation invariant; the two translation-invariant stationary laws of Theorem A are a separate conclusion.

The Gibbs model on Z^7:

- **Corollary B.** One computably specified translation-invariant finite-range interaction on Z^7, with a finite alphabet and energies in {0, 1}, and computable pairwise disjoint rational open intervals J_n of inverse temperature, such that at every inverse temperature in J_n:
  - if U(n) halts, the interaction has exactly one Gibbs measure, with no invariance assumed, and its specification has exponential weak spatial mixing in arbitrary finite volumes. This follows from Theorem 9.5 through Corollary 13.7 of our space-time paper;
  - if U(n) does not halt, it has at least two translation-invariant Gibbs measures and continuum many extremal Gibbs measures.

  This answers Open problems 9.1 and 9.2 of our paper on an uncomputable phase diagram at positive temperature, in dimension seven with finite energies. Version 1.0.0 answered Open problem 9.1, which asks for one translation-invariant finite-range interaction with finite rational energies whose translation-invariant Gibbs measure has undecidable uniqueness at computable rational inverse temperatures. The strengthened corollary also answers Open problem 9.2, which asks for one interaction whose uniqueness among all Gibbs measures, as a function of the inverse temperature, is undecidable.
- **Theorem 9.7 (field response).** Add a field coupled to the global bit carried by live data letters. The pressure is computable and even in the field. At zero field it equals log(1 + (N - 1)e^(-β)), where N is the alphabet size, so it is analytic in β > 0. At every inverse temperature in J_n, the field derivative at zero exists exactly when U(n) halts, and then it is zero. Otherwise the one-sided derivatives are above 119/125 and below -119/125, so the jump exceeds 238/125. This uses only translation-invariant Gibbs facts.
- **Corollary 9.8.** At the rational midpoint of J_n, the right field derivative at zero is upper semicomputable, uniformly in n, but has no uniform computable approximation to error 1/4. No total computable choice of field scale makes the secant slope at that scale smaller than 1/2 on every halting input.

Robustness and effective consequences:

- **Theorem B.1 (robustness).** A positive radius r_n, computable from n without knowing whether U(n) halts, such that every local stochastic table on the same neighbourhood within r_n of the noisy automaton at a rate in I_n (in the largest total-variation distance over parent words) is strictly positive and keeps the label. If U(n) halts, an i.i.d. representation of the table satisfies the exponential all-input bound of Theorem 9.5, uniformly over these tables and rates. If U(n) does not halt, it has two translation-invariant stationary bit laws and continuum many extremal stationary laws. The table's own normalized space-time interaction has exactly one Gibbs measure, with exponential weak spatial mixing in arbitrary volumes, in the halting case, and two translation-invariant and continuum many extremal Gibbs measures otherwise. Perturbations of unnormalized energies are not covered.
- **Corollary 9.9 (finite certificates).** Exponential coalescence is equivalent to a finite strict test, M_H q_H < 1, at some time depth H. These tests define an effectively open set of rates, which picks out exactly the halting windows among the intervals I_n.
- **Corollary 9.10 (forgetting times).** At the rational midpoint of I_n, the first time at which the largest one-site total-variation distance between two deterministic starts falls below 1/2, and the first time at which the all-input noncoalescence probability falls below 1/2, are partial computable functions of n defined exactly on the halting inputs. Neither has a total computable upper bound. The mean depth of all-input coupling from the past is finite on each halting input and has no total computable bound.
- **Corollary 9.11 (coding and exact sampling).** On halting windows the stationary space-time law is a finitary, translation-equivariant factor of a finite-alphabet i.i.d. field on Z^7, with exponential tails for the coding depth, and it is mixing of every order. At rational rates it admits exact finite-window coupling from the past, and its finite marginals are computable by a partial algorithm that terminates on halting inputs. No bound on the running time of the enumeration is claimed.
- **Corollary 9.12 (complexity).** If U is effectively many-one universal, the rational ergodicity set restricted to the union of the intervals I_n is c.e.-complete, and its complement within that union is co-c.e.-complete. For every U, the full set of positive rational rates at which the automaton is ergodic is Pi^0_2, a recalled upper bound; its exact complexity is open.
- **Remark 9.13 (sharper scales, not used).** A multiplicative Chernoff bound would allow smaller constants: k = 26200 and n0 = 458784211 instead of 52386 and 888653587, with the largest window endpoint near 10^(-2.762·10^8) instead of near 10^(-5.350·10^8). The construction keeps the original constants and does not use these values.

Lower dimension (version 1.3.0, Section 10):

- **Theorem C (Theorem 10.1).** One computably specified finite-alphabet, finite-range automaton on Z^4, with computable pairwise disjoint nonempty rational open rate intervals, such that throughout the nth interval uniform whole-symbol replacement is ergodic exactly when U(n) halts. Halting gives exponential coalescence over all initial configurations and attraction from every initial law; nonhalting gives two stationary laws invariant under every translation of Z^4. The rulers and computation boards stay planar; three transverse quorum boxes, marked-parent density (from Section 12 of our forgetting paper, version 2.0.0) and interval sensors control errors.
- **Corollary D.** One computably specified translation-invariant finite-range interaction on Z^5 with energies in {0, 1} and computable rational inverse-temperature windows, on which uniqueness among all Gibbs measures is equivalent to halting; halting also gives exponential weak spatial mixing in arbitrary volumes, and nonhalting gives two translation-invariant Gibbs measures. This answers Open problem 9.2 of our paper on an uncomputable phase diagram in dimension five.
- Theorem C and Corollary D are not formalized in Lean, and the extremal-continuum, field-response and robustness results are stated only for the Z^6 rule.

Scale:

- **Scale (Section 9).** Every guaranteed window lies below 10^(-5·10^8), and the alphabet has more than 10^(10^31539) symbols.

Marsan and Sablik realize every G_delta subset of [0,1] containing 1 as the uniqueness and ergodicity set of a continuous map on the Cantor space under uniform noise. They state that every Pi_2-computable such set is the uniqueness set of a computable map, and that for cellular automata the possible uniqueness sets are still to be characterized. The map here is a cellular automaton: it commutes with shifts and has one finite neighbourhood. The paper does not characterize all noise diagrams of cellular automata. Section 1 gives the full credits.

## Changes in 1.3.0

- New Section 10, Lower dimension: Theorem C (the noise diagram on Z^4) and Corollary D (the Gibbs version on Z^5), with complete proofs. The parameters of the Z^4 rule are certified by two independent exact-arithmetic programs in `verification/z4-scale/`.
- No existing statement, statement number or construction constant changes. The Lean appendix and `lean/` are unchanged.

## Changes in 1.2.0

- **Appendix C (new): Lean formalization.** Theorem A (in the existential form of Theorem 9.3), Corollary 9.4 and the one-rule corollary after Theorem A are proved end to end in Lean 4 with Mathlib, with no `sorry` and no named hypotheses, using only the axioms `propext`, `Classical.choice` and `Quot.sound`. The proof passed a sandboxed comparator run and two independent kernel replays. The sources and records are in `lean/`.
- The verification history now says that the cross-family check of version 1.1.0 re-derived corrections (i)-(iv). Correction (v), the helper-parent count in Proposition 2.1, was found by the Lean development, and the count is proved in Lean.
- No mathematical statement, statement number or construction constant changes.

## Changes in 1.1.0

Corrections to version 1.0.0:

- **Lemma 5.1.** The time-span clause now requires unary zero-potential links to preserve time. The two-terminal clause now requires a positive support edge. The proof of Lemma 5.4, which uses the span clause, now runs a formal clock on its virtual levels.
- **Section 3.2, gate classification.** Version 1.0.0 said that the phase-zero gates are exactly the finite bottom rows of depth d ≥ k. Exceptional phases can have further gate sites of infinite rank. The statement now concerns finite bottom rows only: such a row is a phase-zero gate row exactly when d ≥ k. No argument uses the infinite-rank gate sites.
- **Section 3.2, phase decoder.** The decoder now uses finite approximants instead of infinite liftability. Words of legal charts lie in their own sector's approximant.
- **Lemma 8.4.** The birth-contour clock is stated once: the discrepancy path is drawn one time unit lower instead of shifting the contour.
- **Proposition 2.1.** The proof counted B + 1 helper parents. One of them was already counted, so the right count is B. The parent bound κ is unchanged.

Other changes:

- Corollary B is strengthened as described above. Its version 1.0.0 sentence on uniformly recurrent and periodic Gibbs measures is removed, because uniqueness among all Gibbs measures covers it.
- New results: Theorems 9.5, 9.6 and 9.7, Corollaries 9.8 to 9.12, Remark 9.13, Appendix A (Lemmas A.1-A.5, the finite-history proof of Theorem 9.5) and Appendix B (Theorem B.1).
- The memory estimate in the proof of Theorem 7.3 is sharpened: each bit cylinder now has probability above 122/125, where version 1.0.0 stated 3/4. Theorems 9.6 and 9.7 use this.
- Theorem A, Theorem 9.3 and Corollary 9.4 keep their statements word for word. The construction constants, including k = 52386 and n0 = 888653587, are unchanged, so `verification/` is unchanged.

## Contents and reproduction

- `paper/main.pdf`: the manuscript (59 pages).
- `paper/`: the LaTeX source (`main.tex`), the plain-text abstract and a strict build driver. Run `python -B build.py` there with pdflatex installed. The build disables shell escape, runs pdflatex three times, and rejects warnings, unresolved references and box defects.
- `lean/`: the Lean 4 development of Appendix C (Lean 4.35.0, Mathlib `56a005855ea17e0b0958f73ec801ae140b0a1679`): the statement file, the proofs, the comparator challenge, the axiom audit, the evidence records and the report. `lean/README.md` explains it. The Mathlib dependencies and the two reused cores are fetched, not shipped.
- `verification/scale_check.py`: recomputes the parameters of Section 9 with exact integers and high-precision decimal logarithms, and writes `scale-output.json` and `scale-output.txt` (the recorded outputs are included). It includes a positive control on exact binomial coefficients. Run `python -B scale_check.py` in that directory. It checks the constants that the construction uses; the alternative values of Remark 9.13 are not part of it.
- `verification/z4-scale/`: two independently written exact-arithmetic programs (`verify_scale.py`, Python fractions; `verify_scale.mjs`, Node BigInt) that certify the least parameters k = 43406 and n0 = 713161615 of the Z^4 rule, with their recorded outputs. Run `python -B verify_scale.py`, then `node verify_scale.mjs`, in that directory.
- `SHA256SUMS`: SHA-256 hashes of every shipped file except this manifest. Check with `sha256sum -c SHA256SUMS` from the repository root.

## How it was checked

The paper's AI note and its "Verification status" paragraph give the full account. In short:

- Version 1.0.0: the main theorem and the written manuscript were checked refutation-first by a model from a different developer than the one that wrote it. Corollary B and the scale received a further refutation-first check, which re-derived the corollary's proof and recomputed the scale with an independent program.
- Version 1.1.0: the corrections and new results were found by OpenAI models (GPT-6 Astra and GPT-6.1 Sol), directed by Nidhal Mghirbi. Claude Opus 5.5 verified them refutation-first and independently recomputed both scale choices. That verification took the earlier scaffold and stochastic lemmas as inputs, and it checked the statement and hypotheses of Corollary 13.7 of our space-time paper without re-proving it. Claude Opus 5.5 then read the integrated text back refutation-first.
- Version 1.2.0: the Lean development was written by Claude Opus 5.5 agents, and this version's text by GPT-6.1 Sol. Claude Opus 5.5 read the text back refutation-first against the Lean records.
- Version 1.3.0: Theorem C and Corollary D were found in a GPT-6.1 Sol research run, proved again in an independent blind GPT-6.1 Sol replication, and checked refutation-first by Claude Opus 5.5, which re-derived each step from the source papers; GPT-6.1 Sol wrote this version's text, and its readback found no issue.
- The scale computation is exact or certified to stated precision.
- The theorem rests on the hierarchical scaffold of our paper on an uncomputable phase diagram, cited as an input. Several scaffold facts are formalized in Lean in that paper's Appendix D, as the Verification status says. Theorem A, Corollary 9.4 and the one-rule corollary are formally verified in Lean (Appendix C and `lean/`). The other results, including Corollary B and the results added in version 1.1.0, are written proofs.

## Citation and rights

See `CITATION.cff` for citation metadata. Paper and documentation: CC BY 4.0. Scripts (`paper/build.py`, `verification/scale_check.py`): MIT or Apache 2.0, at your option. See `RIGHTS.md`, the license files and `NOTICE`.
