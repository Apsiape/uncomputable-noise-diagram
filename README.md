# An uncomputable noise diagram on the line and a finite-energy Gibbs diagram on the square lattice

Seth Douglas and Nidhal Mghirbi. Preprint, version 2.1.0, November 2026. [Archive DOI](https://doi.org/10.5281/zenodo.24147268) (all versions); version 2.0.0: [10.5281/zenodo.24352353](https://doi.org/10.5281/zenodo.24352353)

## Abstract

We construct one finite-range cellular automaton on the line with computable disjoint rational windows of uniform replacement noise. Throughout the window indexed by a program, the perturbed automaton is uniformly exponentially ergodic from every initial configuration if the program halts. If it runs forever, a one-site clock observable fails to converge from a specified initial law. The same dichotomy holds at one fixed positive rational noise rate for a computable family of radius-one rules. On the square lattice, the single-rule construction gives one translation-invariant finite-range interaction whose anchored terms have energies zero and one, with a fixed-point-free symmetry of its alphabet. In each halting window of inverse temperature its Dobrushin-Lanford-Ruelle specification has a unique Gibbs measure, with exponential weak spatial mixing. In each nonhalting window it has two translation-invariant Gibbs measures exchanged by the symmetry, under which an odd one-site observable has expectation at least 1/4 and at most -1/4, respectively. The construction uses a hierarchy of fault-tolerant simulations and autonomous spatial signals that encode the noise window.

## Results

- **Theorem A (the line).** One finite-alphabet, translation-invariant, finite-range cellular automaton on Z has computable disjoint nonempty rational open noise windows I_n. At every uniform replacement rate in I_n, it is uniformly exponentially ergodic if U(n) halts; otherwise its laws from a specified initial law fail to converge weakly.
- **Theorem B (the square lattice).** One translation-invariant, finite-range interaction on Z^2 has a finite alphabet, anchored terms with energies in {0,1}, an exact fixed-point-free symmetry of its alphabet and an odd one-site observable M. On computable disjoint nonempty rational open inverse-temperature windows J_n, it has exactly one Dobrushin-Lanford-Ruelle measure, with exponential weak spatial mixing, if U(n) halts; otherwise it has two translation-invariant Dobrushin-Lanford-Ruelle measures, exchanged by the symmetry, under which M has expectation at least 1/4 and at most -1/4, respectively. Nothing is asserted between the windows.
- **Theorem C (a fixed rate on the line).** One positive rational replacement rate and a computable family of finite-alphabet radius-one cellular automata on Z have the same dichotomy: uniform exponential ergodicity on halting inputs and failure of weak convergence from a specified initial law on nonhalting inputs.

These are the exact theorem labels in the introduction. Dimension one for Theorems A and C and dimension two for the finite-energy Theorem B are the smallest possible lattice dimensions. The nonhalting conclusion for the automata is failure of convergence; it does not assert multiple stationary laws.

## Archive contents

- `paper/` contains the manuscript PDF, the LaTeX sources, the plain-text abstract and build instructions.
- The root contains citation metadata, licensing information and `SHA256SUMS`, the SHA-256 digest of every distributed file except the checksum list itself. Verify it from the archive root with `sha256sum -c SHA256SUMS`.

## Build the paper

From `paper/`, run three pdfLaTeX passes:

```sh
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
```

No bibliography program, external images or shell escape is required. The tested engine is MiKTeX-pdfTeX 4.23 (MiKTeX 25.12). [Build instructions](paper/README.txt)

## Changes in version 2.1.0

Theorem B is strengthened: on nonhalting windows the interaction now has two translation-invariant Gibbs measures exchanged by an exact symmetry, with an odd one-site order parameter, and on halting windows the unique Gibbs measure has exponential weak spatial mixing. The interaction is obtained from the space-time interaction of version 2.0.0, which keeps its dichotomy, by blocking with the clock period and doubling. The clock lemma is stated at every site, and several proofs now state hypotheses, regions and margins that version 2.0.0 left implicit. Theorems A and C, all parameters and all existing theorem and lemma numbers are unchanged; Lemmas 7.2 and 7.3 are new. The changes are listed in the paragraph Changes from version 2.0.0 at the end of the introduction.

## Changes in version 2.0.0

A new one-dimensional construction proves the noise diagram for a cellular automaton on the line (Theorem A), a finite-energy Gibbs diagram on the square lattice (Theorem B), and the fixed-rate family on the line (Theorem C). The earlier cellular-automaton constructions on Z^3 through Z^6, their Gibbs constructions on Z^4 through Z^7, and the Lean-checked core and appendix remain in [version 1.4.0](https://doi.org/10.5281/zenodo.24204195). This distribution carries no Lean appendix or Lean library.

## Citation and license

Douglas, Seth, and Nidhal Mghirbi (2026). *An uncomputable noise diagram on the line and a finite-energy Gibbs diagram on the square lattice*. Version 2.1.0. [Archive DOI](https://doi.org/10.5281/zenodo.24147268) · [Citation metadata](CITATION.cff)

Paper and documentation are licensed under CC BY 4.0. [Licensing details](RIGHTS.md)
