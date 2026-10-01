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

The manuscript is written against the frozen Stage-5 A+B theorem package and the Stage-6 Palomar registration record. Stage 8 (arXiv submission) is not performed here.
