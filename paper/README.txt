An uncomputable noise diagram on the line
and a finite-energy Gibbs diagram on the square lattice
Seth Douglas and Nidhal Mghirbi
Version 3.0.0, November 2026

Build from this directory with pdfLaTeX (three passes):

pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex

The tested engine is MiKTeX-pdfTeX 4.23 (MiKTeX 25.12).
No bibliography program, shell escape, package installation or external images
are required. main.pdf is the archive edition, with the version in its date line.

Theorems A and C concern noisy cellular automata on the line. Theorem B gives
one finite-energy square-lattice interaction with EWM on halting windows and
opposite translation-invariant Gibbs states on nonhalting windows; temperatures
between its windows are unclassified.

Theorem D proves that every finite rational magnet has a relatively effectively
open arbitrary-volume EWM set in a rational positive inverse-temperature window.
Theorem E realizes every such effectively open set as the union of nested actual
EWM sets of a computable sequence of magnets with one alphabet and spatial range that may grow;
every stage has magnetic order of magnitude at least 3/8 outside the target set.
Theorem F gives one finite rational nearest-neighbor magnet for each explicitly
specified rational semialgebraic open diagram in z=exp(-beta/d), with exact EWM
there and magnetic order of magnitude at least 1/4 elsewhere in the window.
Three hidden line states per direction suffice and can be necessary within the
ferromagnetic 65536-color Potts class with identical matrices in both
directions and exact periodic Perron weights. Index lists may be very
large; no elementary size bound is claimed. General single-magnet realization
of every effectively open set remains open.

The higher-dimensional constructions and their formalization remain in version
1.4.0: https://doi.org/10.5281/zenodo.24204195
This source distribution has no proof-assistant appendix or library.

Text and documentation: CC BY 4.0. See ../RIGHTS.md.
