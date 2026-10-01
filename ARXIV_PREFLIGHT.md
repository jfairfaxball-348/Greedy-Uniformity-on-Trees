# arXiv packaging and preflight notes

Stage 8 is split into (a) repository-side packaging/preflight and (b) the final human-author arXiv submission. This file documents part (a). It does not authorize or perform part (b).

## Compatibility review

The manuscript uses the standard `article` class with `fontenc`, `inputenc`, `lmodern`, `microtype`, AMS packages, `mathtools`, `booktabs`, `enumitem`, `natbib`, `hyperref`, `cleveref`, and `geometry`. There are no custom style files, figures, external fonts, shell-escape commands, local absolute paths, or repository-relative input dependencies.

The only current arXiv-specific compatibility concern found is arXiv's documented TeX Live 2025 `cleveref` naming issue. arXiv continues to support TeX Live 2023, so the submission record selects TeX Live 2023 rather than altering the publication manuscript.

## Clean-build procedure

The dedicated workflow `.github/workflows/arxiv-preflight.yml` copies only `arxiv/main.tex` and `arxiv/references.bib` (and, after it is frozen, `arxiv/main.bbl`) into a fresh temporary directory. It then builds there with:

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex8 main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

The workflow checks the final log/BLG for unresolved citations/references, BibTeX warnings, multiply defined references, overfull/underfull boxes, and fatal errors; extracts text from the PDF to check title/author/novelty wording; audits the staging directory for generated clutter; and uploads the PDF, log, BLG, and BBL as a preflight artifact for inspection.

The final repository record must identify the exact green bundle commit and CI run.
