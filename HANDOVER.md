# Stage-7 completion handover — ready for Stage 8

**Date:** 2026-10-01  
**Completed:** Stages 1–7  
**Current status:** Stage 7 — research paper, **COMPLETE**  
**Next stage:** Stage 8 — arXiv submission, **NOT STARTED**  
**Stage-7 branch:** `stage7-paper`  
**Stage-7 paper PR:** #6  
**Stage-7 paper merge commit:** `7d99135280949947a15a61233a8c669e1c0ff8ce`  
**Final Stage-7 paper branch head:** `abd61dd85e98b7fd483b906674704fe152f37bdb`  
**Final Stage-7 CI:** GitHub Actions Lean run #170 — **PASS**  
**Manuscript:** `paper/main.tex`  
**Bibliography:** `paper/references.bib`  
**Paper title:** *Greedy Uniformity on Trees: Exact Obstruction and Near-Uniform Spiders*  
**Author:** John Fairfax-Ball  
**Palomar ID:** `PALOMAR-2026-10-01-000003`  
**Palomar version:** 1  
**Palomar trust:** high  
**Registered source commit:** `1733c29a5165148d71a2f0bd1ed2dcd7c35309ce`

Stage 7 is complete. The research manuscript has been written from the frozen,
audited, formalised, and Palomar-registered A+B theorem package and merged to
`main` through PR #6. The final PR head passed the repository's Lean build,
forbidden-placeholder gate, and Python regression suite in GitHub Actions run
#170 before merge. No Stage-8 arXiv submission or arXiv account action was
performed in Stage 7.

The Stage-4 novelty classification remains exactly **plausibly new with bounded
uncertainty**. The manuscript does not claim worldwide priority, an all-(n)
result, a global extremal theorem, a minimizer theorem, optimality, a matching
lower bound, or a converse through well-coveredness.

## Stage-7 manuscript

The publication source is:

    paper/main.tex

with BibTeX database:

    paper/references.bib

and local build notes in:

    paper/README.md

The manuscript is a concise mathematical paper rather than a repository
report. It contains:

- title, author, abstract, introduction, and motivation;
- the random-permutation greedy model, maximal-independent-set law, permutation
  fibres, and total-variation bias;
- literature context and the bounded novelty boundary;
- the exact statement and complete readable proof of Theorem A;
- the mixed-spider construction, exact maximal-independent-set count, and exact
  centre/non-centre probabilities;
- the tuning (l=2^k-k), exact expectation identity, positivity, and both
  asymptotic upper bounds;
- computational evidence clearly separated from proof;
- Lean formalisation and Palomar registration with their proper verification
  scope;
- limitations/open directions;
- acknowledgements, including material AI assistance;
- a complete BibTeX bibliography for the sources used in the paper.

## Frozen theorem boundary in the paper

Theorem A is stated as:

[
G_T=U_T
\iff
T\cong K_1 \text{ or } K_2,
]

equivalently (b(T)=0) exactly in those two cases.

The paper's detailed one-pendant-leaf proof follows the final corrected
permutation-fibre proof. For the local path (x-y-z), swapping the pendant leaf
(x) with its support vertex (y) gives an injection between the two relevant
exact permutation fibres. The direction depends on whether the residual
maximal independent set (A) dominates (z). In both cases an explicit prefix
witness shows that the fibre inclusion is strict. The detailed proof does not
revert to the earlier iid-priority exposition.

The mixed-spider theorem states, for (k\ge0) and (l\ge1), the exact count
(2^k+1) and the exact probabilities

[
p_c=2^{-k}\sum_{j=0}^k \binom{k}{j}\frac1{l+2j+1},
\qquad
q_j=\frac{l+2j}{2^k(l+2j+1)}.
]

For the tuned family (k\ge1), (l=2^k-k), (A=2^k+1),
(J\sim\mathrm{Bin}(k,1/2)), and (W=2J-k), the manuscript states the exact
identity

[
b(T_{k,2^k-k})
=\frac12\left(
\mathbb E\frac{W^2}{A^2(A+W)}
+
\mathbb E\frac{|W|}{A(A+W)}
\right)>0
]

and

[
b(T_{k,2^k-k})
=O\!\left(\frac{\sqrt{k}}{4^k}\right)
=O\!\left(\frac{\sqrt{\log n_k}}{n_k^2}\right),
\qquad
n_k=2^k+k+1.
]

These are exactly the frozen contribution-level claims. The manuscript adds no
all-(n), minimizer, optimality, or matching-lower-bound result.

## Literature and novelty boundary

The related-work discussion follows the final Stage-4 audit rather than
reinterpreting the literature from scratch.

The closest audited source remains Kryven–Versendaal–de Vries,
arXiv:2608.07239v1. Their Proposition 3.8 provides a sufficient
exact-uniformity condition through regular independent sets; the checked source
does not give the converse required for Theorem A. The paper also distinguishes
the contribution-level results from standard/background material including the
random greedy/RSA model, random-priority formulation, dynamic-versus-flat
comparison, elementary first-choice/fibre recurrences, standard
maximal-independent-set counting bounds, and diameter-end tree geometry.

The manuscript uses the exact bounded wording **plausibly new with bounded
uncertainty** and does not present the audit as a worldwide priority
certificate.

## Computational evidence

The paper reports exact computational checks only in a supporting role:

- all 436 nonisomorphic trees on 1–11 vertices were checked, with exactly
  (K_1,K_2) having zero bias;
- direct permutation enumeration and first-vertex recursion agree on all tree
  classes through seven vertices;
- selected exact tuned mixed-spider biases are tabulated;
- the Stage-3 targeted checks cover all 434 tree classes of orders 3–11 and
  1103 one-pendant-leaf paired comparisons.

The paper explicitly states that these computations do not prove the all-tree
obstruction and do not imply a general extremal theorem.

## Lean and Palomar record quoted in the paper

The paper records the original Stage-5 verification environment:

- Lean **4.34.1**;
- Mathlib commit
  `d13f23b723b8a846827a245b89c10fc7d3f11612`.

It separately records the Stage-6 Palomar-compatibility migration:

- Lean **4.35.0-rc3**;
- Mathlib commit
  `c55e6e786f49471c72fbddbec5415808896aec1e`.

The migration is described as packaging compatibility only, with no
strengthening or alteration of the frozen theorem statements.

The paper quotes the final registration accurately:

- ID `PALOMAR-2026-10-01-000003`;
- version 1;
- high trust;
- immutable registered source commit
  `1733c29a5165148d71a2f0bd1ed2dcd7c35309ce`;
- all nine intended theorem declarations present;
- permitted axiom reports exactly
  `[propext, Classical.choice, Quot.sound]`;
- no project-specific mathematical axioms.

The text expressly treats Lean/Palomar as formal-verification and registration
evidence, not as peer review, novelty certification, or a literature-priority
determination.

## Stage-7 verification

The committed manuscript source was compiled locally with the available TeX
toolchain using the equivalent sequence

    pdflatex main.tex
    bibtex8 main
    pdflatex main.tex
    pdflatex main.tex

from the `paper/` directory.

The final build produced a 10-page PDF. The final LaTeX log contained:

- no unresolved citations or cross-references;
- no LaTeX warnings;
- no overfull boxes;
- no underfull boxes;
- no multiply-defined-reference warnings.

The committed GitHub sources were also fetched back and checked against the
locally compiled copies. The resulting Git blob SHAs are:

- `paper/main.tex`:
  `aaec8f050c456e453abc76cacce167613d7c6d45`;
- `paper/references.bib`:
  `afd675585ca2c5918afe72e324d46cd7a16774c7`;
- `paper/README.md`:
  `0f45dc583187bd2921a33a42eecad429b9111576`.

Thus the source that was checked is the source committed in the Stage-7 branch.

## Stage-8 boundary

Stage 8 may begin only from this completed manuscript and handover. It should:

1. re-read this handover and the final `paper/main.tex` /
   `paper/references.bib` sources;
2. verify that the final merged Stage-7 commit is the source being packaged;
3. prepare an arXiv-compatible source bundle without changing the frozen
   mathematical claims;
4. use the paper title and author metadata already in the manuscript unless a
   narrowly targeted submission-format correction is required;
5. use the repository classification `math.CO` as primary and `math.PR` as
   the secondary category unless the responsible author deliberately chooses
   otherwise;
6. preview the compiled arXiv rendering and check bibliography, references,
   page layout, abstract, title, author, categories, licence, and source files;
7. distinguish arXiv submission from public announcement and record the actual
   arXiv identifier/version only after the external submission succeeds.

Do not strengthen the novelty wording or theorem scope during arXiv packaging.
If arXiv requires a formatting-only change, keep it narrowly isolated and
recompile before submission.

**No Stage-8 action has been performed in this Stage-7 session.**
