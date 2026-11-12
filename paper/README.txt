One noisy cellular automaton with an uncomputable noise diagram
Seth Douglas and Nidhal Mghirbi
Version 1.2.0, November 2026

Build: python -B build.py [--build-dir NEW_OR_EMPTY_DIRECTORY]
Requires Python 3 and pdflatex with the packages loaded by main.tex (including aliascnt). The bibliography is inline. The build runs pdflatex three times without shell escape and rejects warnings, unresolved references and overfull or underfull boxes. main.pdf is the compiled preprint (43 pages). abstract.txt is the abstract as plain text; appendix-lean.tex is included by main.tex.

Version 1.2.0 adds the Lean formalization appendix and updates the verification account. Theorem A, in the existential form of Theorem 9.3, Corollary 9.4 and the one-rule corollary after Theorem A are proved end to end, without sorry or named hypotheses, using only propext, Classical.choice and Quot.sound. Appendix C gives the exact scope, proof-route differences, pins and recorded checks. No mathematical statement, statement number or construction constant changes. The paper's "Changes from version 1.1.0" and "Changes from version 1.0.0" paragraphs record the version history.

The Lean sources and verification records are in lean/ of the release repository. Its README-ARXIV.md gives the recorded reproduction setup and commands. Dependencies and the reused cores in vendor/ are fetched, not shipped. The scale computation of Section 9 is in verification/scale_check.py of the release repository; the alternative values of Remark 9.13 are not part of that script. No publication or submission is performed by the paper build.
