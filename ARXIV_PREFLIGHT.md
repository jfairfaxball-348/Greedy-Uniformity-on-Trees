# arXiv packaging and preflight notes

Stage 8 was split into (a) repository-side packaging/preflight and (b) the final human-author arXiv submission. This file records the completed pre-submission part (a). The final submission has since occurred; see `ARXIV_SUBMISSION.md` for the live publication record.

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

## Final verified bundle

The frozen upload bundle is the `arxiv/` directory at commit
`14b3c6ecbbf423eebefa8f673124793f3e3f3c02`. It contains exactly
`main.tex`, `references.bib`, and `main.bbl`.

GitHub Actions arXiv preflight run **#7** at that exact commit passed. Its final
artifact ID is `11149926165` and artifact digest is
`sha256:507e4813e0f8c0a0dece20506be50e8f40a3ac5789874e4b9242c2c3b2d5d88e`.
The final build used pdfTeX / TeX Live 2023 and standard BibTeX, produced a
10-page PDF, regenerated a `main.bbl` byte-for-byte identical to the frozen
bundle file, and passed the warning/reference/rendered-text gates.

The final-run PDF SHA-256 is
`39f2e4944d269ce974e7150bfa23bde6668096afbbc6294a267a30eed8b614ac`;
the generated/frozen BBL SHA-256 is
`ba54dacfb08fce17c8e33f89f6ec982c34028eec71281ef466fee987b1377e1f`.

The PDF was rendered to images and visually checked across all 10 pages. No
clipped text, overlaps, broken glyphs, truncated equations, malformed table,
or broken page layout was found. A render comparison with the immediately
preceding green standalone build reported zero changed pages out of ten;
the differing raw PDF hashes are attributable to build-level PDF metadata.

Packaging/preflight was completed before the author submission and is retained here as the reproducible package record.

## Post-submission record

The verified bundle was subsequently submitted and is now live as [`arXiv:2610.02276`](https://arxiv.org/abs/2610.02276), version 1, submitted 2026-10-01. arXiv lists `math.CO` as the primary subject and `math.PR` as secondary, provides the DataCite DOI [`10.48550/arXiv.2610.02276`](https://doi.org/10.48550/arXiv.2610.02276), and links the submission licence as CC BY 4.0.
