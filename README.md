# Computability of noise, mixing and correlation diagrams

## An uncomputable disorder line in a zero-field Ising crystal

Seth Douglas and Nidhal Mghirbi. Preprint, version 4.0.0, November 2026. [Archive DOI](https://doi.org/10.5281/zenodo.24147268) (all versions); version 4.0.0: [10.5281/zenodo.24608702](https://doi.org/10.5281/zenodo.24608702); version 3.0.0: [10.5281/zenodo.24569235](https://doi.org/10.5281/zenodo.24569235); version 2.1.0: [10.5281/zenodo.24408026](https://doi.org/10.5281/zenodo.24408026); version 2.0.0: [10.5281/zenodo.24352353](https://doi.org/10.5281/zenodo.24352353)

Versions 1.0.0 to 3.0.0 were titled *An uncomputable noise diagram on the line and a finite-energy Gibbs diagram on the square lattice*.

## Abstract

Which temperature sets can one finite magnet realize through its correlations? On [87/4, 45/2], a zero-field Ising model with exchanges in {-1,+1} has a sampled spin correlation that changes, at a right-computably enumerable inverse temperature of halting degree, from positive strictly decreasing decay to an asymptotically damped cosine of period three in units of a fixed vector d. Its nonplanar degree-three graph has 32 vertices per geometric cell, about 4.7 x 10^22 spins per signed repeat, and |d| ~ 1.8 x 10^10 lattice spacings. One Gibbs state, exponential weak mixing and analytic pressure persist throughout the window. Every fixed-lag correlation is computable, but no computable lag or signal guarantee follows from a prescribed distance above the cut, and no sampled correlation in the window is negative before lag 10^329. More generally, for every relatively effectively open subset W of a positive rational window, a periodic +/-1 sign pattern on this fixed geometry, obtained effectively from an enumeration of W, makes W the oscillatory set of a sampled spin correlation; the converse assumes uniqueness and the all-lag sign promise. For finite rational magnets, negative point-field response somewhere has exactly the relatively effectively open diagrams under uniqueness. These results complement a noise diagram on the line, a mixing/order diagram on the square lattice, effective openness of mixing sets, their sequential realization, and exact realization of explicit semialgebraic diagrams. Realizing every relatively effectively open mixing set by one magnet with opposite order on its complement remains open.

## Results

- **Theorem A (the line).** One finite-alphabet, translation-invariant, finite-range cellular automaton on Z has computable disjoint nonempty rational open noise windows I_n. At every uniform replacement rate in I_n, it is uniformly exponentially ergodic if U(n) halts; otherwise its laws from a specified initial law fail to converge weakly.
- **Theorem B (the square lattice).** One translation-invariant, finite-range interaction on Z^2 has a finite alphabet, anchored terms with energies in {0,1}, an exact fixed-point-free symmetry of its alphabet and an odd one-site observable M. On computable disjoint nonempty rational open inverse-temperature windows J_n, it has exactly one Dobrushin-Lanford-Ruelle measure, with exponential weak spatial mixing, if U(n) halts; otherwise it has two translation-invariant Dobrushin-Lanford-Ruelle measures, exchanged by the symmetry, under which M has expectation at least 1/4 and at most -1/4, respectively. Nothing is asserted between the windows.
- **Theorem C (a fixed rate on the line).** One positive rational replacement rate and a computable family of finite-alphabet radius-one cellular automata on Z have the same dichotomy: uniform exponential ergodicity on halting inputs and failure of weak convergence from a specified initial law on nonhalting inputs.
- **Theorem D (effective openness).** For every finite rational magnet on Z^2 (a translation-invariant finite-range interaction with a finite alphabet, rational energies, a fixed-point-free alphabet involution and an odd one-site observable) and every rational window 0 < a < b, the set of inverse temperatures in [a,b] with arbitrary-volume exponential weak spatial mixing is relatively effectively open, uniformly from the interaction table, its range and a, b.
- **Theorem E (sequential realization).** Given rational 0 < a < b and an enumerator of a relatively effectively open W in [a,b], one can compute a sequence of finite rational magnets whose mixing sets are nested and have union W. Every stage has magnetic order with gap 3/8 at every inverse temperature outside W. The stages share one alphabet, involution and observable; their finite horizontal range may grow. Nothing is asserted for a stage between its own mixing set and W.
- **Theorem F (explicit semialgebraic diagrams).** Given rational 0 < a < b, an integer d >= 1 and an explicitly specified rational semialgebraic open set U, one can compute one finite rational nearest-neighbor magnet whose arbitrary-volume exponential-weak-mixing set in [a,b] is exactly the set of inverse temperatures with exp(-beta/d) in U, with magnetic order with gap 1/4 at every other inverse temperature in the window. At most three hidden line states per direction suffice; three can be necessary within ferromagnetic 65536-color Potts line decorations with identical matrices in both directions and exact periodic Perron weights.
- **Theorem G (response-sign diagrams).** Given rational 0 < a < b and an enumerator of a relatively effectively open W in [a,b], one computes one finite rational magnet on Z^2 that has exactly one Dobrushin-Lanford-Ruelle measure, arbitrary-volume exponential weak spatial mixing and real-analytic pressure at every inverse temperature in [a,b], and whose response to a field at one site is negative somewhere exactly on W. The response vanishes off one column; along the column it is eventually negative on W, and off W it is nonnegative everywhere. Conversely, for every finite rational magnet with exactly one Dobrushin-Lanford-Ruelle measure throughout the window, the set where the response is negative somewhere is relatively effectively open, uniformly in the data.
- **Theorem H (Ising decay-shape diagrams).** Given rational 0 < a < b and an enumerator of a relatively effectively open W in [a,b], an effective construction gives one periodic sign pattern in {-1,+1} on a fixed nonplanar 32-vertex, three-regular geometric graph, a site and a period vector d. The zero-field Ising model with these signs has, throughout the window, exactly one Dobrushin-Lanford-Ruelle measure, uniform arbitrary-volume exponential weak mixing, and real-analytic pressure and finite marginals. Off W the spin correlation sampled along d is positive and strictly decreasing; on W it is asymptotically a damped cosine of period three in units of d, with exactly two nearest singularities, both simple poles. Conversely, uniqueness throughout the window and the all-lag sign promise make the oscillatory set relatively effectively open. H is an algorithmic existence proof; a compiler from enumerator code is not included.
- **Theorem I (an explicit crystal).** On the same geometry, explicit periodic signs give one zero-field Ising model with every exchange in {-1,+1}. On the window [87/4, 45/2] it has exactly one Dobrushin-Lanford-Ruelle measure, uniform arbitrary-volume exponential weak mixing, and real-analytic pressure and finite marginals. With o = (552699460,0,0) and d = (0,17686381696,0), the mean-zero spin correlation sampled along d is positive and strictly decreasing for beta <= beta_star and has the two-simple-pole cosine form of Theorem H for beta > beta_star. The cut beta_star is right-computably enumerable and has exactly the Turing degree of the halting set. This is a disorder line: a change of decay shape within the mixing regime.
- **Finite-data limits for I.** Every fixed-lag correlation is computable. No total computable N(k) bounds a negative sampled lag for all beta >= beta_star + 2^(-k) in the window, and no total computable epsilon(k) > 0 guarantees a negative lag of magnitude at least epsilon(k) there. No sampled correlation in the window is negative before lag 10^329.
- **Proposition (a finite hidden Markov stationary row).** A translation-invariant synchronous probabilistic cellular automaton on Z with finite alphabet, finite radius and strictly positive transition probabilities, having a spatially stationary invariant row law that is the output of a stationary finite-state hidden Markov chain, is uniformly exponentially ergodic; its space-time specification has exactly one Dobrushin-Lanford-Ruelle measure and arbitrary-volume exponential weak mixing.

Whether one finite magnet realizes every relatively effectively open mixing set, with opposite order on its complement, remains open.

These are the exact theorem labels in the introduction. Theorem statements A-F are unchanged from version 3.0.0.

## Archive contents

- `paper/` contains the manuscript PDF, the LaTeX sources, the plain-text abstract and build instructions.
- `paper/programs/` contains the Python programs and data for the finite checks of Theorem I: the Boolean circuit certificate, the scattering check and the crystal checks. The manuscript's software-checks page states exactly what these checks prove.
- The root contains citation metadata, licensing information and `SHA256SUMS`, the SHA-256 digest of every distributed file except the checksum list itself. Verify it from the archive root with `sha256sum -c SHA256SUMS`.

## Build the paper

From `paper/`, run three pdfLaTeX passes:

```sh
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
```

No bibliography program, external images or shell escape is required. The tested engine is MiKTeX-pdfTeX 4.23 (MiKTeX 25.12). [Build instructions](paper/README.txt)

## Reproduce the finite checks

From `paper/programs/`, with Python 3.10 or later and the standard library only:

```sh
python -I -B export_circuit.py
python -I -B reference_scattering.py
python -I -B certify_circuit.py
python -I -B verify_results.py
python -I -B crystal.py check
```

Expected: PASS in both verifiers, 85041 final gates, 323 input bits, 164852 Walsh terms, 68 arithmetic blocks and 1024 selection rows. CIRCUIT-CERTIFICATE.json contains the full SHA-256 object digests.

## Changes in version 4.0.0

Theorem G adds exact response-sign diagrams and their uniqueness converse. Theorems H and I add sampled Ising decay-shape diagrams on a fixed nonplanar geometry and an explicit zero-field Ising crystal whose disorder line sits at a right-computably enumerable inverse temperature of halting degree, together with finite-data limits, a Boolean circuit identity certified on all inputs, and its exact thermal reduction. A new proposition proves exponential forgetting for positive line probabilistic cellular automata with a finite hidden Markov stationary row. The title changes to reflect the new results. Theorems A-F and their proofs are retained. The changes are listed in the paragraph Changes from version 3.0.0 at the end of the introduction.

## Changes in version 3.0.0

Theorems D-F add effective openness for finite rational magnets, sequential realization of every relatively effectively open set of inverse temperatures, and exact single-magnet realization of every explicitly specified rational semialgebraic open diagram in an exponential temperature coordinate. New lemmas prove the correlated local-alarm estimate and empty-sector ancestry used in Theorem E. Theorems A-C and their proofs are unchanged in substance. The changes are listed in the paragraph Changes from version 2.1.0 at the end of the introduction.

## Changes in version 2.1.0

Theorem B is strengthened: on nonhalting windows the interaction now has two translation-invariant Gibbs measures exchanged by an exact symmetry, with an odd one-site order parameter, and on halting windows the unique Gibbs measure has exponential weak spatial mixing. The interaction is obtained from the space-time interaction of version 2.0.0, which keeps its dichotomy, by blocking with the clock period and doubling. The clock lemma is stated at every site, and several proofs now state hypotheses, regions and margins that version 2.0.0 left implicit. Theorems A and C, all parameters and all existing theorem and lemma numbers are unchanged; Lemmas 7.2 and 7.3 are new. The changes are listed in the paragraph Changes from version 2.0.0 at the end of the introduction.

## Changes in version 2.0.0

A new one-dimensional construction proves the noise diagram for a cellular automaton on the line (Theorem A), a finite-energy Gibbs diagram on the square lattice (Theorem B), and the fixed-rate family on the line (Theorem C). The earlier cellular-automaton constructions on Z^3 through Z^6, their Gibbs constructions on Z^4 through Z^7, and the Lean-checked core and appendix remain in [version 1.4.0](https://doi.org/10.5281/zenodo.24204195). This distribution carries no Lean appendix or Lean library.

## Citation and license

Douglas, Seth, and Nidhal Mghirbi (2026). *Computability of noise, mixing and correlation diagrams: an uncomputable disorder line in a zero-field Ising crystal*. Version 4.0.0. [Archive DOI](https://doi.org/10.5281/zenodo.24147268) · [Citation metadata](CITATION.cff)

Paper and documentation are licensed under CC BY 4.0; the programs under MIT or Apache-2.0, at your option. [Licensing details](RIGHTS.md)
