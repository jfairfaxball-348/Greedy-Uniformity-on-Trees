# arXiv packaging and preflight notes

Stage 8 is split into (a) repository-side packaging/preflight and (b) the final human-author arXiv submission. This file documents part (a). It does not authorize or perform part (b).

## Compatibility review

The manuscript uses the standard `article` class with `fontenc`, `inputenc`, `lmodern`, `microtype`, AMS packages, `mathtools`, `booktabs`, `enumitem`, `natbib`, `hyperref`, `cleveref`, and `geometry`. There are no custom style files, figures, external fonts, shell-escape commands, local absolute paths, or repository-relative input dependencies.

The only current arXiv-specific compatibility concern found is arXiv's documented TeX Live 2025 `cleveref` naming issue. arXiv continues to support TeX Live 2023, so the submission record selects TeX Live 2023 rather than altering the publication manuscript.

## Clean-build procedure

The dedicated workflow `.github/workflows/arxiv-preflight.yml` copies only `arxiv/main.tex` and `arxiv/references.bib` into a fresh temporary directory. It then builds there with the standard arXiv-style BibTeX sequence:

```sh
pdflatex -interaction=nonstopmode -halt-on-error main.tex
bibtex main
pdflatex -interaction=nonstopmode -halt-on-error main.tex
pdflatex -interaction=nonstopmode -halt-on-error main.tex
```

If `arxiv/main.bbl` has been frozen into the bundle, the workflow also checks that a clean regeneration from `references.bib` is byte-for-byte identical.

The workflow checks the final log/BLG for unresolved citations/references, BibTeX warnings, multiply defined references, overfull/underfull boxes, and fatal errors; extracts text from the PDF to check title/author/novelty wording; audits the staging directory for generated clutter; and uploads the PDF, log, BLG, and BBL as a preflight artifact for inspection.

The first clean compile on GitHub Actions confirmed TeX Live 2023 and produced a 10-page PDF; its preflight gate failed only because the earlier `bibtex8` invocation emitted a locale-CS-file diagnostic. The workflow now uses standard `bibtex`, matching arXiv's normal BibTeX path rather than suppressing that diagnostic.

The final repository record must identify the exact green bundle commit and CI run.
