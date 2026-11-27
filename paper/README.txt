Computability of noise, mixing and correlation diagrams
An uncomputable disorder line in a zero-field Ising crystal
Seth Douglas and Nidhal Mghirbi
Version 4.0.0, November 2026

Build from this directory with three passes:

pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex

No bibliography program, external images, installation or shell escape is
required. main.pdf is built from these sources. abstract.txt is the exact
LaTeX abstract. The AI disclosure in main.tex is retained from version 3.0.0.

Theorems A and C concern full-state forgetting versus nonconvergence for
positive-noise cellular automata on the line. A uses one rule and disjoint
halting-program windows; C uses a computable family at one fixed rate.
Theorem B gives one finite-energy interaction on the square lattice, with
one DLR state and arbitrary-volume exponential weak mixing on halting
windows, and opposite translation-invariant ordered states on nonhalting
windows. Other temperatures are unclassified.

Theorem D makes every finite rational magnet's EWM set relatively effectively
open in a positive rational window. E realizes every such set as the union
of nested actual EWM sets of a computable sequence, each ordered outside the
target. F realizes an explicitly given rational semialgebraic open diagram
in an exponential coordinate by one nearest-neighbor magnet, ordered on its
complement. Theorem statements A-F are retained verbatim from version 3.0.0.

Theorem G realizes every relatively effectively open set W by one finite
rational magnet as its set with a negative point-field response somewhere.
All off-column responses vanish; column responses are eventually negative
on W and eventually positive off W. One DLR state, arbitrary-volume EWM and
analytic pressure hold throughout. Its converse assumes uniqueness on the
window and is uniform also in the rational observable. The hidden Markov
proposition proves full exponential forgetting for strictly positive line
PCA with a finite hidden Markov stationary row. Its decoration consequence
requires fresh sampling from a finite old hidden neighborhood and the site's
new hidden symbol, ignoring the decoration's own earlier values.

Theorem H realizes every relatively effectively open W in a rational positive
window as the oscillatory set of one sampled microscopic spin correlation
on a fixed nonplanar 32-vertex, degree-three Ising geometry. Signs are +/-1,
there is no field, and the sign pattern, the site and the period vector d
are computed once per enumeration. Off W the sampled correlation is positive and strictly
decreasing at every lag; on W its asymptotic cosine has period three in
units of d and exactly two simple nearest poles. One DLR state, EWM and
analytic pressure persist throughout. The converse assumes uniqueness and
the all-lag sign promise. H is an algorithmic existence proof; a general
compiler from enumerator code is not included. Its square-lattice variant
uses bonds in {-1,0,+1} on nearest and diagonal pairs.

Theorem I is a separate explicit crystal, built from its own 2^105-state
binary-energy parent. On beta in [87/4,45/2], one mean-zero microscopic spin
sampled along d=(0,17686381696,0) has positive strictly decreasing decay
through a right-c.e. cut of halting degree and an asymptotically damped
cosine above it, of period three in units of d. One DLR state, EWM and
analytic pressure hold everywhere in that window. Its graph has 32
vertices per geometric cell, degree three, and is nonplanar. Its signed repeat contains exactly
46752085813280748601344 spins; one sampled lag spans 17686381696 geometric
lattice spacings and four parent lags. On the monotone side the real simple
pole shares its circle with two non-pole singularities, including at the cut.
This is a disorder line, a change of decay shape within the mixing regime.

Each fixed-lag correlation is computable. No total computable N(k) bounds a
negative sampled lag for all beta >= beta_star + 2^(-k), and no computable
positive epsilon(k) guarantees a negative signal of that magnitude there.
No parent negative correlation occurs through lag 10^330 anywhere in the
parent window [1/4,1/2]. The scale 10^2536 is an estimate only. These are
asymptotic results, with no finite-data method for locating the cut.

The general single-magnet mixing-phase question remains open: arbitrary
relatively effectively open EWM set with opposite translation-invariant
ordered states on its complement. G and H relate through sampled correlation
sets; no all-displacement response assertion is made for I.

Finite reproduction from programs/ (Python 3.10 or later, standard library only):

python -I -B export_circuit.py
python -I -B reference_scattering.py
python -I -B certify_circuit.py
python -I -B verify_results.py
python -I -B crystal.py check

Expected: PASS in both verifiers, 85041 final gates, 323 input bits,
164852 Walsh terms, 68 arithmetic blocks and 1024 selection rows.
CIRCUIT-CERTIFICATE.json contains the full SHA-256 object digests.
The manuscript's software-checks page states precisely what these checks
prove. The reproducibility appendix lists the remaining printer queries.

Archive: https://doi.org/10.5281/zenodo.24147268

The archive root holds SHA256SUMS (every distributed file except the checksum
list itself), CITATION.cff and the licensing files.

Text and documentation: CC BY 4.0. Programs in programs/: MIT or Apache-2.0,
at your option. See ../RIGHTS.md.
