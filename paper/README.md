# Paper source

The Stage-7 manuscript is `main.tex` with BibTeX database `references.bib`.

Build from this directory with:

```sh
latexmk -pdf -bibtex main.tex
```

Clean generated files with:

```sh
latexmk -C
```

The manuscript is written against the frozen Stage-5 A+B theorem package and the Stage-6 Palomar registration record. Stage 8 is complete: the paper is live as [`arXiv:2610.02276`](https://arxiv.org/abs/2610.02276), version 1, submitted 2026-10-01, with arXiv-issued DOI [`10.48550/arXiv.2610.02276`](https://doi.org/10.48550/arXiv.2610.02276) and CC BY 4.0 licence.
