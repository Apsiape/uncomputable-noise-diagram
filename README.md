# An uncomputable noise diagram on the line and a finite-energy Gibbs diagram on the square lattice

Seth Douglas and Nidhal Mghirbi. Preprint, version 3.0.0, November 2026. [Archive DOI](https://doi.org/10.5281/zenodo.24147268) (all versions); version 2.1.0: [10.5281/zenodo.24408026](https://doi.org/10.5281/zenodo.24408026); version 2.0.0: [10.5281/zenodo.24352353](https://doi.org/10.5281/zenodo.24352353)

## Abstract

Which sets of noise rates or inverse temperatures can separate rapid forgetting from persistent order? We construct one finite-range cellular automaton on the line with computable disjoint rational noise windows: throughout a program's window it is uniformly exponentially ergodic if the program halts, whereas a one-site clock fails to converge from a specified initial law otherwise. The same dichotomy holds at one fixed positive rational rate for a computable family of radius-one rules. On the square lattice, one finite-energy interaction has arbitrary-volume exponential weak spatial mixing in halting windows and opposite translation-invariant Gibbs states in nonhalting windows. We then study the full mixing set of finite rational magnets in a positive rational inverse-temperature window. Every such set is relatively effectively open. Conversely, every effectively open set is the union of nested actual mixing sets of a computable sequence of magnets with a common alphabet; every stage has opposite ordered states outside the target set, and the spatial range of the stages may grow. For every explicitly specified rational semialgebraic open diagram in an exponential temperature coordinate, one finite nearest-neighbor magnet has exactly that mixing set and is ordered everywhere else in the window. At most three hidden line states per direction suffice, and three can be necessary for ferromagnetic 65536-color Potts line decorations with identical matrices in both directions and exact periodic Perron weights. Whether one finite magnet realizes every effectively open set remains open.

## Results

- **Theorem A (the line).** One finite-alphabet, translation-invariant, finite-range cellular automaton on Z has computable disjoint nonempty rational open noise windows I_n. At every uniform replacement rate in I_n, it is uniformly exponentially ergodic if U(n) halts; otherwise its laws from a specified initial law fail to converge weakly.
- **Theorem B (the square lattice).** One translation-invariant, finite-range interaction on Z^2 has a finite alphabet, anchored terms with energies in {0,1}, an exact fixed-point-free symmetry of its alphabet and an odd one-site observable M. On computable disjoint nonempty rational open inverse-temperature windows J_n, it has exactly one Dobrushin-Lanford-Ruelle measure, with exponential weak spatial mixing, if U(n) halts; otherwise it has two translation-invariant Dobrushin-Lanford-Ruelle measures, exchanged by the symmetry, under which M has expectation at least 1/4 and at most -1/4, respectively. Nothing is asserted between the windows.
- **Theorem C (a fixed rate on the line).** One positive rational replacement rate and a computable family of finite-alphabet radius-one cellular automata on Z have the same dichotomy: uniform exponential ergodicity on halting inputs and failure of weak convergence from a specified initial law on nonhalting inputs.
- **Theorem D (effective openness).** For every finite rational magnet on Z^2 (a translation-invariant finite-range interaction with a finite alphabet, rational energies, a fixed-point-free alphabet involution and an odd one-site observable) and every rational window 0 < a < b, the set of inverse temperatures in [a,b] with arbitrary-volume exponential weak spatial mixing is relatively effectively open, uniformly from the interaction table, its range and a, b.
- **Theorem E (sequential realization).** Given rational 0 < a < b and an enumerator of a relatively effectively open W in [a,b], one can compute a sequence of finite rational magnets whose mixing sets are nested and have union W. Every stage has magnetic order with gap 3/8 at every inverse temperature outside W. The stages share one alphabet, involution and observable; their finite horizontal range may grow. Nothing is asserted for a stage between its own mixing set and W.
- **Theorem F (explicit semialgebraic diagrams).** Given rational 0 < a < b, an integer d >= 1 and an explicitly specified rational semialgebraic open set U, one can compute one finite rational nearest-neighbor magnet whose arbitrary-volume exponential-weak-mixing set in [a,b] is exactly the set of inverse temperatures with exp(-beta/d) in U, with magnetic order with gap 1/4 at every other inverse temperature in the window. At most three hidden line states per direction suffice; three can be necessary within ferromagnetic 65536-color Potts line decorations with identical matrices in both directions and exact periodic Perron weights.

Whether one finite magnet realizes every relatively effectively open set remains open.

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

## Changes in version 3.0.0

Theorems D-F add effective openness for finite rational magnets, sequential realization of every relatively effectively open set of inverse temperatures, and exact single-magnet realization of every explicitly specified rational semialgebraic open diagram in an exponential temperature coordinate. New lemmas prove the correlated local-alarm estimate and empty-sector ancestry used in Theorem E. Theorems A-C and their proofs are unchanged in substance. The changes are listed in the paragraph Changes from version 2.1.0 at the end of the introduction.

## Changes in version 2.1.0

Theorem B is strengthened: on nonhalting windows the interaction now has two translation-invariant Gibbs measures exchanged by an exact symmetry, with an odd one-site order parameter, and on halting windows the unique Gibbs measure has exponential weak spatial mixing. The interaction is obtained from the space-time interaction of version 2.0.0, which keeps its dichotomy, by blocking with the clock period and doubling. The clock lemma is stated at every site, and several proofs now state hypotheses, regions and margins that version 2.0.0 left implicit. Theorems A and C, all parameters and all existing theorem and lemma numbers are unchanged; Lemmas 7.2 and 7.3 are new. The changes are listed in the paragraph Changes from version 2.0.0 at the end of the introduction.

## Changes in version 2.0.0

A new one-dimensional construction proves the noise diagram for a cellular automaton on the line (Theorem A), a finite-energy Gibbs diagram on the square lattice (Theorem B), and the fixed-rate family on the line (Theorem C). The earlier cellular-automaton constructions on Z^3 through Z^6, their Gibbs constructions on Z^4 through Z^7, and the Lean-checked core and appendix remain in [version 1.4.0](https://doi.org/10.5281/zenodo.24204195). This distribution carries no Lean appendix or Lean library.

## Citation and license

Douglas, Seth, and Nidhal Mghirbi (2026). *An uncomputable noise diagram on the line and a finite-energy Gibbs diagram on the square lattice*. Version 3.0.0. [Archive DOI](https://doi.org/10.5281/zenodo.24147268) · [Citation metadata](CITATION.cff)

Paper and documentation are licensed under CC BY 4.0. [Licensing details](RIGHTS.md)
