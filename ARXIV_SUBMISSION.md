# arXiv Stage-8 submission record

**Status:** packaging/preflight in progress; no arXiv submission has been created.

## Metadata

- **Title:** Greedy Uniformity on Trees: Exact Obstruction and Near-Uniform Spiders
- **Author:** John Fairfax-Ball
- **Abstract:** use the abstract in `arxiv/main.tex` verbatim.
- **Primary category:** `math.CO`
- **Secondary category:** `math.PR`
- **Suggested comments:** `10 pages; no figures.`
- **Journal reference:** none asserted.
- **DOI:** none asserted.
- **Report number:** none asserted.
- **Affiliation / ORCID / institutional email / funding:** not asserted; do not invent.
- **Manuscript source base:** repository `main` commit `083ddf8abcb87a3a60f0c4e32eb79df49128766e`.
- **Submission processor:** `pdflatex`.
- **arXiv TeX Live selection:** **TeX Live 2023**. arXiv documents a TeX Live 2025 `cleveref` issue; selecting the supported 2023 environment avoids changing the frozen manuscript solely for that upstream package issue.

## Source bundle

The upload staging directory is `arxiv/`. It is intentionally self-contained and contains only publication sources needed by arXiv:

- `main.tex` — exact copy of `paper/main.tex` from the source base above;
- `references.bib` — exact copy of `paper/references.bib`;
- `main.bbl` — to be added from the clean preflight build if the generated bibliography is clean and matches the source.

No `.aux`, `.log`, `.out`, `.toc`, `.fls`, `.fdb_latexmk`, `.synctex.gz`, editor metadata, repository material, figures, or unrelated generated files belong in the upload bundle.

The main file has no input/include dependencies outside this directory, no shell-escape requirement, no external build step, no local absolute paths, and no figures.

## Bibliography workflow

The manuscript uses `natbib` with `plainnat`. arXiv currently supports BibTeX processing from a submitted `.bib`, and also uses a matching pre-generated `.bbl` when one is present. The preflight therefore generates `main.bbl` and freezes it into the bundle after verification. The `.bib` is retained as source provenance.

The Stage-7 bibliography metadata is preserved, including:

- Krivelevich--Mészáros--Michaeli--Shikhelman: *Random Structures & Algorithms* 64(4), 986--1015 (2024);
- Alice Contat: *Journal of Applied Probability* 59(4), 1042--1058 (2022).

## Frozen scope and novelty audit

The upload source must preserve the frozen A+B theorem package. In particular:

- Theorem A is the exact obstruction `G_T=U_T` iff `T` is `K_1` or `K_2`, equivalently zero bias only in those cases.
- Theorem B gives the exact mixed-spider count and probabilities, the tuned exact positive-bias identity, and **upper bounds only** of orders `O(sqrt(k)/4^k)` and `O(sqrt(log n_k)/n_k^2)`.
- There is no all-`n` result, minimizer theorem, global extremal theorem, optimality theorem, matching lower bound, or worldwide-priority claim.
- Novelty status remains exactly **plausibly new with bounded uncertainty**.
- Lean/Palomar are described only as formal-verification/registration evidence, not peer review or novelty certification.

## arXiv licence: human choice required

Do **not** select a licence automatically. arXiv currently offers these submission choices:

- CC BY 4.0;
- CC BY-SA 4.0;
- CC BY-NC-SA 4.0;
- CC BY-NC-ND 4.0;
- arXiv.org perpetual, non-exclusive licence 1.0;
- CC0.

The author must choose the arXiv licence at submission time. The repository's Apache-2.0 licence is separate and does not determine this choice.

## Human-input / submission-time items

Before the final submit action, the human author must:

1. choose the arXiv licence;
2. confirm any account/endorsement prompts arXiv presents;
3. select `pdflatex` and TeX Live 2023;
4. verify the generated arXiv PDF against the preflight PDF;
5. review title, author, abstract, categories, comments, and source-file list;
6. perform the final submit action only after approving the preview.

No arXiv identifier/version is to be recorded until arXiv actually accepts the submission.
