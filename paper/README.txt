One noisy cellular automaton with an uncomputable noise diagram
Seth Douglas and Nidhal Mghirbi
Version 1.0.0, November 2026

Build: python -B build.py [--build-dir NEW_OR_EMPTY_DIRECTORY]
Requires Python 3 and pdflatex with the packages loaded by main.tex (including aliascnt). The bibliography is inline. The build runs pdflatex three times without shell escape and rejects warnings, unresolved references and overfull or underfull boxes. main.pdf is the compiled preprint (28 pages). abstract.txt is the abstract as plain text.
The scale computation of Section 9 is in ../verification/scale_check.py. No publication or submission is performed by the build.
