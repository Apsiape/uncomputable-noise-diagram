An uncomputable noise diagram on the line
and a finite-energy Gibbs diagram on the square lattice
Seth Douglas and Nidhal Mghirbi
Version 2.1.0, November 2026

Build from this directory with pdfLaTeX (three passes):

pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex
pdflatex -no-shell-escape -interaction=nonstopmode -halt-on-error main.tex

The tested engine is MiKTeX-pdfTeX 4.23 (MiKTeX 25.12).
The three passes resolve the table of contents, citations and cross-references.
No bibliography program, external images or shell escape is required.

main.pdf is the archive edition, with the version in the date line.
The arXiv edition uses the date November 2026. Its PDF, sources and source
package are in ../arxiv/. Extract paper-arxiv.tar.gz into an empty directory
and run the same three commands there. The two editions differ only in the
date line and the paragraph Changes from version 2.0.0, which appears only
in the archive edition.

Theorems A and C concern cellular automata on the line. Theorem B concerns
one finite-energy interaction on the square lattice. The higher-dimensional
constructions and their Lean appendix are in version 1.4.0:
https://doi.org/10.5281/zenodo.24204195
This distribution carries no Lean appendix or Lean library.

Text and documentation: CC BY 4.0. See ../RIGHTS.md.
