# One noisy cellular automaton with an uncomputable noise diagram

Seth Douglas and Nidhal Mghirbi. Version 1.0.0, November 2026.

**This is a preprint. It has not been peer reviewed.**

## Abstract

Can varying only the noise rate of one cellular automaton encode the halting problem? We construct one computably specified cellular automaton on Z^6, with a finite alphabet and a finite neighbourhood, whose ergodicity under uniform replacement noise does so. There are pairwise disjoint open intervals I_n with rational endpoints computable from n such that, at every rate in I_n, the perturbed automaton is ergodic exactly when a fixed universal machine halts on input n. In the nonhalting case it has at least two translation-invariant stationary laws; in the halting case it has one stationary law attracting every initial law.

Finite rulers in a hierarchical tiling turn the noise rate into a cutoff in a sequence of local flags. Computation boards read that cutoff and simulate the selected input. A threshold checker preserves a global bit when the computation does not halt. When it halts, interval-valued sensors erase every surviving chart, and a common-noise coupling removes dependence on every initial state. The guaranteed intervals accumulate at zero and lie at astronomically small rates. The space-time Gibbs correspondence gives a finite-energy interaction on Z^7 with undecidable translation-invariant Gibbs uniqueness. Thus one fixed local rule has an uncomputable noise diagram.

## What the paper proves

Fix a universal machine U whose halting set is undecidable.

- **Theorem A (Theorem 9.3).** One computably specified cellular automaton on Z^6, with a finite alphabet and a finite neighbourhood, and computable pairwise disjoint open intervals I_n with rational endpoints, such that at every rate in I_n uniform whole-symbol replacement makes the automaton ergodic exactly when U(n) halts. Nonhalting gives at least two translation-invariant stationary laws. Halting gives a unique stationary law attracting every initial law.
- **Corollary 9.4.** For this fixed automaton, deciding ergodicity at a rational noise rate is undecidable, even under the promise that the rate lies in one of the intervals I_n.
- **Corollary B.** One computably specified translation-invariant finite-range interaction on Z^7, with a finite alphabet and energies in {0, 1}, and computable pairwise disjoint rational intervals J_n of inverse temperature, on which the Gibbs measure invariant under all translations of Z^7 is unique exactly when U(n) halts. This answers Open problem 9.1 of our paper on the undecidable phase diagram in dimension seven. In the halting case this measure is also the only uniformly recurrent, and hence the only periodic, Gibbs measure.
- **Scale (Section 9).** Every guaranteed window lies below 10^(-5·10^8), and the alphabet has more than 10^(10^31539) symbols.

Marsan and Sablik realize every G_delta subset of [0,1] containing 1 as the uniqueness and ergodicity set of a continuous map on the Cantor space under uniform noise. They state that every Pi_2-computable such set is the uniqueness set of a computable map, and that for cellular automata the possible uniqueness sets are still to be characterized. The map here is a cellular automaton: it commutes with shifts and has one finite neighbourhood. The paper does not characterize all noise diagrams of cellular automata. Section 1 gives the full credits.

## Contents and reproduction

- `paper/main.pdf`: the manuscript (28 pages).
- `paper/`: the LaTeX source (`main.tex`), the plain-text abstract and a strict build driver. Run `python -B build.py` there with pdflatex installed. The build disables shell escape, runs pdflatex three times, and rejects warnings, unresolved references and box defects.
- `verification/scale_check.py`: recomputes the parameters of Section 9 with exact integers and high-precision decimal logarithms, and writes `scale-output.json` and `scale-output.txt` (the recorded outputs are included). It includes a positive control on exact binomial coefficients. Run `python -B scale_check.py` in that directory.
- `SHA256SUMS`: SHA-256 hashes of every shipped file except this manifest. Check with `sha256sum -c SHA256SUMS` from the repository root.

## How it was checked

The paper's AI note and its "Verification status" paragraph give the full account. In short:

- The main theorem and the written manuscript were checked refutation-first by a model from a different developer than the one that wrote it. Corollary B and the scale received a further refutation-first check, which re-derived the corollary's proof and recomputed the scale with an independent program.
- The scale computation is exact or certified to stated precision.
- The theorem rests on the hierarchical scaffold of our paper on the undecidable phase diagram, cited as an input. Several scaffold facts are formalized in Lean in that paper's Appendix D, as the Verification status says. The main theorem of this paper is not formalized.

## Citation and rights

See `CITATION.cff` for citation metadata. Paper and documentation: CC BY 4.0. Scripts (`paper/build.py`, `verification/scale_check.py`): MIT or Apache 2.0, at your option. See `RIGHTS.md`, the license files and `NOTICE`.
