# Stage-5 completion handover — ready for Stage 6

**Date:** 2026-09-30  
**Completed:** Stages 1–5  
**Current status:** Stage 5 — Lean formalisation, **COMPLETE**  
**Next stage:** Stage 6 — Palomar registration, **NOT STARTED**  
**Frozen A merge:** PR #3 → `main`, merge commit `3d624b55c81af3d078f9419addcf953aedc23e8b`  
**Frozen B merge:** PR #4 → `main`, merge commit `240dd7ecfef52041541509083422010438c278d3`  
**Verified A+B code head:** `47802b8a18a92847e447e88c02ecb42620b3da09`  
**Substantive verification workflow:** GitHub Actions run **#161**  
**Completed branch verification:** GitHub Actions run **#162** at `1bc26af933609b520c86412f792e5a92f65e311d`

The Stage-4 novelty classification remains **plausibly new with bounded uncertainty**. Do not upgrade it to worldwide-priority certainty. No all-\(n\) extremal, minimizer, optimality, matching-lower-bound, or “uniform greedy law implies well-covered” claim has been added.

## Stage-5 completion record

Run #161 passed the complete combined A+B root build:

- `lake build` completed successfully — **8954 jobs**;
- the forbidden-placeholder check passed, covering `sorry`, `admit`, and `native_decide`;
- `python -m pytest -q` passed — **5 passed**.

`GreedyUniformity/AxiomCheck.lean` inspected the two final A statements and all seven final B checkpoints. Every printed axiom set is exactly:

    [propext, Classical.choice, Quot.sound]

There are no project-specific mathematical axioms in the final theorem package.

## Frozen Theorem A

Frozen A remains the stable dependency merged through PR #3:

    tree_greedyLawEqUniform_iff_isK1OrK2
    tree_bias_eq_zero_iff_isK1OrK2

It was not reopened mathematically during the B integration.

## Frozen Theorem B

Final B1 theorem:

    mixedSpider_maximalIndependentSets_card

formalises `|MIS(T_{k,l})| = 2^k + 1` in the frozen regime.

Final B2 theorems:

    greedyProb_mixedSpiderCenter
    greedyProb_mixedSpiderNoncenter

formalise the exact finite permutation-law formulas

    p_c = 2^{-k} * Σ_{j=0}^k binom(k,j)/(l + 2j + 1)

and, for a particular type-j non-centre maximal independent set,

    q_j = (l + 2j)/(2^k * (l + 2j + 1)).

Final B3 theorems:

    bias_mixedSpider_tuned_eq_expectation
    bias_mixedSpider_tuned_pos
    bias_mixedSpider_tuned_isBigO
    bias_mixedSpider_tuned_isBigO_sqrt_log_order_div_order_sq

cover the tuning `l = 2^k-k`, the exact Stage-3 expectation identity, positive bias for `k>0`, and

    b(T) = O(sqrt(k)/4^k)

together with, along `n_k = 2^k+k+1`,

    b(T) = O(sqrt(log n_k)/n_k^2).

The formalisation exposed only Lean elaboration/API integration issues; the frozen B mathematics and theorem scope were not strengthened.

## Pinned environment

- Lean: **4.34.1**
- Toolchain: `leanprover/lean4:v4.34.1`
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`
- Exact dependency lock: `lake-manifest.json`
- CI: `.github/workflows/lean.yml`

Do not casually change these versions.

## Next-session boundary

Stage 6 is the next permitted stage. PR #4 is merged into `main`; begin the next session by reading the then-current repository state and the current Palomar requirements. Do not redo Stages 1–5 unless a narrowly targeted correction is forced by verified evidence.

Stage 7 (paper writing) and Stage 8 (arXiv submission) remain blocked until the fixed workflow reaches them.
