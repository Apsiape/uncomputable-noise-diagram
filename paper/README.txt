One noisy cellular automaton with an uncomputable noise diagram
Seth Douglas and Nidhal Mghirbi
Version 1.3.0, November 2026

Build: python -B build.py [--build-dir NEW_OR_EMPTY_DIRECTORY]
Requires Python 3 and pdflatex with the packages loaded by main.tex (including aliascnt). The bibliography is
inline. The build runs pdflatex three times without shell escape and rejects warnings, unresolved references and
overfull or underfull boxes. main.pdf is the compiled preprint (59 pages). abstract.txt is the abstract as plain
text; lower-dimension.tex (Section 10) and appendix-lean.tex (Appendix C) are included by main.tex.

Version 1.3.0 adds Theorem C, one fixed finite-alphabet finite-range automaton on Z^4 whose rational rate windows
encode halting, with exponential all-input coalescence on halting windows and two translation-invariant stationary
laws on nonhalting windows; and Corollary D, one fixed translation-invariant finite-range {0,1}-energy interaction
on Z^5 whose uniqueness among all Gibbs measures, on computable inverse-temperature windows, is equivalent to
halting. Section 10 proves both. All earlier statements and statement numbers, the Z^6 and Z^7 results and the Lean
appendix are unchanged. Theorem C and Corollary D are not formalized in Lean.

The Lean sources and records of Appendix C are in lean/ of the release repository; lean/README.md explains them.
The scale of the Z^6 construction is checked by verification/scale_check.py; the parameters of the Z^4 rule
(k = 43406, n0 = 713161615) are certified by two independent exact-arithmetic programs in verification/z4-scale/.
No publication or submission is performed by the build.
