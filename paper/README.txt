One noisy cellular automaton with an uncomputable noise diagram
Seth Douglas and Nidhal Mghirbi
Version 1.4.0, November 2026

Theorem E gives one fixed finite-alphabet finite-range cellular automaton on Z^3 with computable rational noise-rate windows encoding halting. Halting gives exponential all-input full-symbol coalescence with a fixed positive computable coefficient; nonhalting gives two fully translation-invariant stationary laws. Corollary F gives its fixed finite-range {0,1}-energy space-time interaction on Z^4, uniqueness among all Gibbs measures iff halting, and exponential weak spatial mixing. Complete proofs are in Section 11, dimension-three.tex.

All earlier statements and numbers are retained. The Z^3 and Z^4 automaton results and their Gibbs corollaries are not formalized. Appendix C describes the original Lean development and its scope.

Paper files: main.tex, lower-dimension.tex, dimension-three.tex, appendix-lean.tex, abstract.txt, build.py and main.pdf (72 pages). The bibliography is inline.

Build from this directory with Python 3 and pdflatex, with the LaTeX packages loaded by main.tex installed:
  python -I -B build.py --build-dir ../build-fresh
The build directory must be new or empty. build.py runs pdflatex three times without shell escape and rejects warnings, unresolved references, and overfull or underfull boxes. The resulting PDF is copied to main.pdf.

Independent scale certificates and recorded outputs for Section 11 are in ../verification/z3-scale/. The Python program uses only the standard library; the Node program uses native BigInt and standard modules. See that directory's README.txt for commands and arithmetic details. The certified recipe has k=43429, n0=33644133613821753975, binding term (64K_full)^(-44), and c=1/(2^42*17600000000*(4^43429+176363)).
