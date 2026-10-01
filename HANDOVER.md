# Stage-8 packaging/preflight handover — awaiting author arXiv submission

**Date:** 2026-10-01  
**Completed:** Stages 1–7; Stage-8 repository packaging/preflight  
**Current status:** arXiv package fully prepared and verified  
**Remaining action:** final arXiv submission by the human author after explicit approval  
**Packaging branch:** `stage8-arxiv-packaging`  
**Packaging PR:** #8  
**Stage-7 source base on `main`:** `083ddf8abcb87a3a60f0c4e32eb79df49128766e`  
**Frozen arXiv bundle commit:** `14b3c6ecbbf423eebefa8f673124793f3e3f3c02`  
**Bundle directory:** `arxiv/`  
**Paper title:** *Greedy Uniformity on Trees: Exact Obstruction and Near-Uniform Spiders*  
**Author:** John Fairfax-Ball  
**Primary category:** `math.CO`  
**Secondary category:** `math.PR`  
**Palomar ID:** `PALOMAR-2026-10-01-000003`, version 1, high trust  
**Registered Palomar source:** `1733c29a5165148d71a2f0bd1ed2dcd7c35309ce`

The repository-side packaging/preflight portion of Stage 8 is complete. No
arXiv submission has been created, no arXiv licence has been selected, no final
submit action has been taken, and no arXiv identifier/version exists yet.

## Frozen upload bundle

The exact upload bundle is the `arxiv/` directory at commit
`14b3c6ecbbf423eebefa8f673124793f3e3f3c02`. It contains only:

- `main.tex` — exact Stage-7 manuscript copy, Git blob
  `aaec8f050c456e453abc76cacce167613d7c6d45`;
- `references.bib` — exact Stage-7 bibliography copy, Git blob
  `afd675585ca2c5918afe72e324d46cd7a16774c7`;
- `main.bbl` — verified generated bibliography, Git blob
  `53b6e9a8adbcd1ec000ca44fbc5df1c4b43bded7`.

Do not upload repository files outside `arxiv/`, and do not add generated
`.aux`, `.log`, `.out`, `.toc`, `.fls`, `.fdb_latexmk`,
`.synctex.gz`, PDF, editor metadata, or temporary files.

The source is self-contained: there are no external `input`/`include`
dependencies, figures, shell-escape requirements, local absolute paths, custom
fonts, or external build steps.

## Verified preflight

GitHub Actions arXiv preflight run **#7** at exact bundle commit
`14b3c6ecbbf423eebefa8f673124793f3e3f3c02` passed under pdfTeX / TeX
Live 2023 using the sequence:

    pdflatex -interaction=nonstopmode -halt-on-error main.tex
    bibtex main
    pdflatex -interaction=nonstopmode -halt-on-error main.tex
    pdflatex -interaction=nonstopmode -halt-on-error main.tex

The frozen `main.bbl` is byte-for-byte identical to a fresh regeneration.
The final build produced a 10-page PDF with all citations and cross-references
resolved. The automated gate found no undefined citations/references,
multiply-defined references, overfull boxes, underfull boxes, fatal LaTeX
errors, or BibTeX warnings.

Final-run artifact:

- artifact ID: `11149926165`;
- artifact digest:
  `sha256:507e4813e0f8c0a0dece20506be50e8f40a3ac5789874e4b9242c2c3b2d5d88e`;
- PDF SHA-256:
  `39f2e4944d269ce974e7150bfa23bde6668096afbbc6294a267a30eed8b614ac`;
- BBL SHA-256:
  `ba54dacfb08fce17c8e33f89f6ec982c34028eec71281ef466fee987b1377e1f`.

The PDF was rendered and visually inspected across all 10 pages. Title, author,
abstract, theorem statements, equations, table, bibliography, hyperlinks, and
page layout render cleanly. A renderer-level comparison with the immediately
preceding green standalone build showed zero changed pages out of ten.

Because arXiv currently documents a TeX Live 2025 `cleveref` naming issue,
the submission should use **pdfLaTeX / TeX Live 2023**. The verified TeX Live
2023 rendering has correct theorem/lemma/section reference names.

## Frozen mathematical and novelty boundary

Do not alter the A+B theorem package while submitting.

Theorem A remains exactly:

    G_T = U_T  iff  T is K_1 or K_2,

equivalently zero total-variation bias exactly in those two cases.

Theorem B remains the exact mixed-spider count and probabilities, the tuned
exact positive-bias expectation identity, and the two **upper bounds only**

    O(sqrt(k)/4^k)
    O(sqrt(log n_k)/n_k^2).

There is no all-`n` theorem, minimizer theorem, global extremal theorem,
optimality theorem, matching lower bound, or worldwide-priority claim.

The novelty classification remains exactly **plausibly new with bounded
uncertainty**. Lean and Palomar remain formal-verification/registration
evidence only, not peer review or novelty certification.

## Submission metadata

Use `ARXIV_SUBMISSION.md` as the canonical submission record. In particular:

- title: *Greedy Uniformity on Trees: Exact Obstruction and Near-Uniform Spiders*;
- author: John Fairfax-Ball;
- abstract: copy the recorded abstract verbatim;
- primary category: `math.CO`;
- secondary category: `math.PR`;
- neutral suggested comments: `10 pages; no figures.`;
- journal reference: blank / none asserted;
- DOI: blank / none asserted;
- report number: blank / none asserted;
- do not invent affiliation, ORCID, institutional email, funding, or other
  metadata not supplied by the author.

## Final arXiv submission instructions

The next session/action is the human-author submission step only. Proceed as
follows after the author explicitly instructs final submission:

1. Log in to the author's arXiv account and start a new submission.
2. Set the primary category to `math.CO` and secondary category to
   `math.PR`.
3. Upload exactly the three files from the frozen `arxiv/` bundle:
   `main.tex`, `references.bib`, and `main.bbl`.
4. Select `pdflatex` and **TeX Live 2023**.
5. Enter the title, author, abstract, and comments from
   `ARXIV_SUBMISSION.md`; leave journal reference, DOI, and report number
   unasserted.
6. **The author must personally choose the arXiv licence.** The repository
   Apache-2.0 licence does not determine the arXiv submission licence.
7. Compile/preview on arXiv. Verify the title page, abstract, theorem and lemma
   reference names, formulas, Table 1, bibliography, URLs/commit hashes, and
   all 10 pages against the preflight rendering.
8. Recheck the source-file list and metadata. Do not introduce promotional,
   priority, optimality, all-`n`, minimizer, or matching-lower-bound wording.
9. Only after the author reviews and approves that preview should the final
   **Submit** action be taken.
10. After arXiv actually accepts the submission and returns an identifier,
    record the identifier/version, submitted source commit, licence choice, and
    acceptance status in the repository. Until then, do not claim that the
    paper is on arXiv.

If arXiv's generated preview differs materially from the verified TeX Live
2023 preflight, stop before final submission and diagnose the rendering
difference rather than silently changing mathematics or bibliography.

## Remaining boundary

This handover authorizes no final arXiv action by itself. The intended state is:

**arXiv package fully prepared and verified; final submission awaiting explicit
author instruction.**
