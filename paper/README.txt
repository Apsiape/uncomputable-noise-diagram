One noisy cellular automaton with an uncomputable noise diagram
Seth Douglas and Nidhal Mghirbi
Version 1.1.0, November 2026

Build: python -B build.py [--build-dir NEW_OR_EMPTY_DIRECTORY]
Requires Python 3 and pdflatex with the packages loaded by main.tex (including aliascnt). The bibliography is inline. The build runs pdflatex three times without shell escape and rejects warnings, unresolved references and overfull or underfull boxes. main.pdf is the compiled preprint (40 pages). abstract.txt is the abstract as plain text.
Version 1.1.0 corrects and extends version 1.0.0; the paper's "Changes from version 1.0.0" paragraph lists the changes.
The scale computation of Section 9 is in ../verification/scale_check.py. Version 1.1.0 keeps the construction constants that it checks; the alternative values of Remark 9.13 are not part of that script. No publication or submission is performed by the build.
