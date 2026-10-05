# Final project handover — arXiv publication recorded

**Status refresh:** 2026-10-05  
**Workflow:** all eight stages complete  
**Paper title:** *Greedy Uniformity on Trees: Exact Obstruction and Near-Uniform Spiders*  
**Author:** John Fairfax-Ball  
**arXiv:** [`arXiv:2610.02276`](https://arxiv.org/abs/2610.02276), version 1  
**arXiv v1 submitted:** 2026-10-01 10:07:00 UTC  
**Primary category:** `math.CO`  
**Secondary category:** `math.PR`  
**arXiv-issued DOI:** [`10.48550/arXiv.2610.02276`](https://doi.org/10.48550/arXiv.2610.02276)  
**arXiv licence:** CC BY 4.0  
**Palomar:** `PALOMAR-2026-10-01-000003`, version 1, high trust  
**Registered Palomar source:** `1733c29a5165148d71a2f0bd1ed2dcd7c35309ce`  
**Frozen arXiv bundle commit:** `14b3c6ecbbf423eebefa8f673124793f3e3f3c02`  
**Bundle directory:** `arxiv/`

## Completion state

The fixed eight-stage programme is complete:

1. repository scaffold;
2. detailed prior-art and novelty audit;
3. informal proof;
4. final theorem-specific prior-art/uniqueness audit;
5. Lean formalisation of the frozen theorem package;
6. Palomar registration;
7. research paper;
8. arXiv submission.

The publication record is now live at `arXiv:2610.02276`. This replaces the previous handover state in which final author submission was still pending.

## Frozen upload bundle

The submitted publication source was prepared from the verified `arxiv/` bundle at commit
`14b3c6ecbbf423eebefa8f673124793f3e3f3c02`. It contains:

- `main.tex` — Git blob `aaec8f050c456e453abc76cacce167613d7c6d45`;
- `references.bib` — Git blob `afd675585ca2c5918afe72e324d46cd7a16774c7`;
- `main.bbl` — Git blob `53b6e9a8adbcd1ec000ca44fbc5df1c4b43bded7`.

The source is self-contained and has no external `input`/`include` dependencies, figures, shell-escape requirements, local absolute paths, custom fonts, or external build steps.

## Verified preflight

GitHub Actions arXiv preflight run **#7** at the frozen bundle commit passed under pdfTeX / TeX Live 2023 with standard BibTeX. The run produced a 10-page PDF with resolved citations and cross-references and no gate-triggering undefined references, multiply-defined references, overfull/underfull boxes, fatal LaTeX errors, or BibTeX warnings.

Final-run record:

- artifact ID: `11149926165`;
- artifact digest: `sha256:507e4813e0f8c0a0dece20506be50e8f40a3ac5789874e4b9242c2c3b2d5d88e`;
- PDF SHA-256: `39f2e4944d269ce974e7150bfa23bde6668096afbbc6294a267a30eed8b614ac`;
- BBL SHA-256: `ba54dacfb08fce17c8e33f89f6ec982c34028eec71281ef466fee987b1377e1f`.

The PDF was also rendered and visually inspected across all 10 pages before submission.

## Frozen mathematical and novelty boundary

Theorem A remains exactly the classification

```text
G_T = U_T  iff  T is K_1 or K_2,
```

equivalently zero total-variation bias exactly in those two cases.

Theorem B remains the exact mixed-spider count and probabilities, the tuned exact positive-bias expectation identity, and the two **upper bounds only**

```text
O(sqrt(k)/4^k)
O(sqrt(log n_k)/n_k^2).
```

There is no all-`n` theorem, minimizer theorem, global extremal theorem, optimality theorem, matching lower bound, or worldwide-priority claim.

The final novelty classification remains **plausibly new with bounded uncertainty**. Lean and Palomar are formal-verification/registration evidence, not peer review or novelty certification.

## Canonical records

- `ARXIV_SUBMISSION.md` — completed arXiv metadata and publication record;
- `ARXIV_PREFLIGHT.md` — frozen package/preflight evidence;
- `PALOMAR_SUBMISSION.md` — Palomar registration record;
- `CLAIMS.md` — theorem/claim ledger and current project boundary;
- `ROADMAP.md` — eight-stage completion record.

No further workflow stage remains. Any future work should be treated as post-publication maintenance or a new research extension rather than continuation of the original eight-stage programme.
