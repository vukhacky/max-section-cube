# Mathematical source

`Maximal_Sections_of_the_Cube_Geometric_Proof.tex` is the self-contained LaTeX source used for the formalization and computational supplement. Its bibliography is embedded in the source; no separate BibTeX file is required.

The source uses strong induction on section dimension, with fibers of dimension two less. The main theorem is labelled `thm:full-balanced-value`; the rational comparison is in the appendix labelled `sec:comparisons`.

Build with a LaTeX installation providing the packages listed in the preamble:

```bash
pdflatex Maximal_Sections_of_the_Cube_Geometric_Proof.tex
pdflatex Maximal_Sections_of_the_Cube_Geometric_Proof.tex
```

The programs named `verify_pairs.py` and `verify_pairs_independent.py` in the manuscript are provided in `../computation/`. Their generated outputs reproduce the arithmetic verification. The manuscript hash and the certificate parameters are recorded in `../computation/manifest.json`.

The formal proof covers the main upper bound, attainment, and equality classification. See `../docs/FORMALIZATION.md` for its precise relationship to the manuscript's further results.
