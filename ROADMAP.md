# Roadmap

The project follows this fixed sequence.

1. **Scaffold repository — COMPLETE (2026-09-29).**
2. **Detailed prior-art and novelty audit — COMPLETE (2026-09-29).** Verdict: **PASS FOR PROOF** with bounded novelty uncertainty.
3. **Prove the selected theorem — COMPLETE INFORMALLY (2026-09-29).** A complete structural proof establishes (G_T=U_T) iff (T\cong K_1) or (K_2), and proves the mixed-spider near-uniform construction.
4. **Final prior-art/uniqueness check against the theorem actually proved — COMPLETE (2026-09-29).** Verdict: **PASS — FREEZE FOR FORMALISATION.** A and B are each classified as **plausibly new with bounded uncertainty**. Standard proof ingredients are separated from contribution-level claims.
5. **Formalise the frozen theorem in Lean — COMPLETE (2026-09-30).** The Stage-5 A+B package was verified under Lean 4.34.1 / Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. GitHub Actions run **#161** at `47802b8a18a92847e447e88c02ecb42620b3da09` passed the complete root build, forbidden-placeholder rejection, and **5** Python tests. All final A and B `#print axioms` checkpoints reported exactly `[propext, Classical.choice, Quot.sound]`.
6. **Complete Palomar registration — COMPLETE (2026-10-01).** Registered as **PALOMAR-2026-10-01-000003**, version 1, with **high** trust. The immutable Palomar source commit is `1733c29a5165148d71a2f0bd1ed2dcd7c35309ce`, preserving all two final A declarations and seven final B checkpoints. Current Palomar policy required a packaging-only migration to Lean 4.35.0-rc3 / Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`; the frozen theorem statements were not strengthened.
7. **Write the research paper — COMPLETE (2026-10-01).** The concise LaTeX manuscript `paper/main.tex` and BibTeX database `paper/references.bib` present the frozen A+B theorem package, the corrected strict permutation-fibre proof of Theorem A, the exact mixed-spider calculation, supporting computation, bounded literature context, and the Lean/Palomar verification record. The source compiled to a 10-page PDF with references/citations resolved and no LaTeX warnings or overfull/underfull boxes.
8. **Complete arXiv submission — COMPLETE (2026-10-01).** The self-contained `arxiv/` bundle frozen at commit `14b3c6ecbbf423eebefa8f673124793f3e3f3c02` passed source-scope, reference/citation, warning, bibliography, and visual PDF checks under TeX Live 2023 with standard BibTeX. The resulting paper is live as [`arXiv:2610.02276`](https://arxiv.org/abs/2610.02276), version 1, submitted 2026-10-01 in `math.CO` with `math.PR` secondary; the arXiv-issued DataCite DOI is [`10.48550/arXiv.2610.02276`](https://doi.org/10.48550/arXiv.2610.02276), and the recorded licence is CC BY 4.0.

The novelty wording remains **plausibly new with bounded uncertainty**. Do not
reopen the frozen A+B mathematics except for a narrowly targeted correction
genuinely forced by integration or discovered verification evidence. All eight
stages are complete; the final publication record is `arXiv:2610.02276` v1.
