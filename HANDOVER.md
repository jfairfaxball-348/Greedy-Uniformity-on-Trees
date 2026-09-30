# Stage-5 continuation handover — Frozen Theorem B integration

**Date:** 2026-09-30  
**Completed:** Stages 1–4; Stage-5 finite-law bridge; Frozen Theorem A  
**Current stage:** Stage 5 — Lean formalisation, **IN PROGRESS**  
**Current B branch:** `stage5-theorem-b`  
**Open B pull request:** #4, `Stage 5: formalise Frozen Theorem B`  
**Pre-handover B code head:** `0d7827002876d0b149c55a136a263254163fc967`  
**Last fully green workflow checkpoint:** `aad5dda57dfdc026bc5032eab448efbee521fb47` (run #111)  
**Do not begin:** Stages 6–8 until the full Frozen A+B package is CI-green and the B axiom audit is verified.

The Stage-4 novelty classification remains **plausibly new with bounded uncertainty**. No worldwide-priority, all-n extremal, minimizer, optimality, matching-lower-bound, or “uniform greedy law implies well-covered” claim has been added.

## Repository integration state

Frozen Theorem A was merged through PR #3 into `main` at merge commit

    3d624b55c81af3d078f9419addcf953aedc23e8b

and is treated as a stable dependency.

Frozen Theorem B is being integrated through PR #4 on

    stage5-theorem-b

The substantive B source modules and final theorem statements are present. The remaining work is final root-build integration and verification, not a change to the frozen mathematics.

The latest completed full-root CI before this handover was run **#135** at

    9976bcd1b4cb3ca3b69759ac5d507817a1f1a148

and failed only in `GreedyUniformity/MixedSpiderBias.lean`, after successfully building through `GreedyUniformity.MixedSpiderProbability`.

Run #135 reported two integration errors:

1. an unqualified `center` constructor in `mixedSpiderCenterSet_not_mem_noncenter_image`;
2. a denominator rewrite in `bias_mixedSpider_eq_formulaBias` being attempted after the maximal-independent-set set had already been expanded.

Both were repaired in code commit

    0d7827002876d0b149c55a136a263254163fc967

by qualifying `MixedSpiderVertex.center` and moving `mixedSpider_uniform_denominator` before the structural MIS rewrite.

At this handover, that repair has not yet received a completed CI result. Therefore **Stage 5 must not yet be marked complete**.

## Frozen Theorem B source status

### B1 — maximal-independent-set count

The mixed spider `T_{k,l}` is formalised with explicit vertex constructors and adjacency rules. The maximal independent sets are structurally classified as the unique centre-containing set plus one non-centre set for each subset of the k length-two arms.

Final B1 theorem:

    GreedyUniformity.mixedSpider_maximalIndependentSets_card

stating, in the frozen regime `0 < l`,

    |MIS(T_{k,l})| = 2^k + 1.

### B2 — exact finite permutation-law probabilities

The proof uses the repository's exact finite permutation model, with arm-orientation classes, relevant-vertex first-position counts, exceptional-order counts, exact fibre cardinalities, and the bridge to `greedyProb`.

Final B2 theorems:

    GreedyUniformity.greedyProb_mixedSpiderCenter
    GreedyUniformity.greedyProb_mixedSpiderNoncenter

These formalise the frozen formulas

    p_c = 2^{-k} * Σ_{j=0}^k binom(k,j)/(l + 2j + 1)

and, for a non-centre set with j inner-arm choices,

    q_j = (l + 2j) / (2^k * (l + 2j + 1)).

The auxiliary exact closed-form layer includes `mixedSpiderCenterFormula`, `mixedSpiderNoncenterFormula`, and the binomial/powerset regrouping lemmas.

### B3 — tuned sparse-bias family

The tuned parameter is

    mixedSpiderTunedL k = 2^k - k.

The exact Stage-3 expectation identity is formalised through

    GreedyUniformity.bias_mixedSpider_tuned_eq_expectation

with the finite expectation expression `mixedSpiderTunedExpectation k`.

The positive-bias statement is

    GreedyUniformity.bias_mixedSpider_tuned_pos

for `0 < k`.

The two frozen asymptotic conclusions are

    GreedyUniformity.bias_mixedSpider_tuned_isBigO
    GreedyUniformity.bias_mixedSpider_tuned_isBigO_sqrt_log_order_div_order_sq

corresponding to

    b(T_{k,2^k-k}) = O(sqrt(k) / 4^k)

and, along

    n_k = 2^k + k + 1,

    b(T_{k,2^k-k}) = O(sqrt(log n_k) / n_k^2).

No lower bound, all-n theorem, or optimality statement has been introduced.

## Important B modules

The current B chain includes:

- `GreedyUniformity/MixedSpider.lean`
- `GreedyUniformity/MixedSpiderMIS.lean`
- `GreedyUniformity/MixedSpiderFormula.lean`
- `GreedyUniformity/MixedSpiderTuned.lean`
- `GreedyUniformity/MixedSpiderBiasFormula.lean`
- `GreedyUniformity/MixedSpiderOrderCount.lean`
- `GreedyUniformity/FirstInFinset.lean`
- `GreedyUniformity/MixedSpiderRelevant.lean`
- `GreedyUniformity/MixedSpiderExceptional.lean`
- `GreedyUniformity/MixedSpiderFibreCount.lean`
- `GreedyUniformity/MixedSpiderProbability.lean`
- `GreedyUniformity/MixedSpiderBias.lean`
- `GreedyUniformity/MixedSpiderMoments.lean`
- `GreedyUniformity/MixedSpiderAsymptotic.lean`
- `GreedyUniformity/MixedSpiderOrderAsymptotic.lean`
- `GreedyUniformity/TheoremB.lean`

`GreedyUniformity.lean` imports `TheoremB`, so the final verification is a true combined A+B root build.

## Axiom audit status

`GreedyUniformity/AxiomCheck.lean` now requests `#print axioms` for all seven final B checkpoints:

    mixedSpider_maximalIndependentSets_card
    greedyProb_mixedSpiderCenter
    greedyProb_mixedSpiderNoncenter
    bias_mixedSpider_tuned_eq_expectation
    bias_mixedSpider_tuned_pos
    bias_mixedSpider_tuned_isBigO
    bias_mixedSpider_tuned_isBigO_sqrt_log_order_div_order_sq

The previously verified Frozen A final theorems report exactly

    [propext, Classical.choice, Quot.sound]

No final claim is made yet about the B axiom output because no CI-green full-root run containing the complete B audit has completed. The next session must inspect and record the actual output rather than assume it matches A.

There are no intended project-specific mathematical axioms, `sorry`, `admit`, or `native_decide`.

## Verification history

The last completely green workflow on the B branch is run **#111** at

    aad5dda57dfdc026bc5032eab448efbee521fb47

which passed the workflow checks then present:

- `lake build`;
- forbidden-placeholder rejection;
- Python regression tests.

After adding the final root import / axiom integration, CI exposed a sequence of pinned-Mathlib elaboration/API issues. These were repaired without changing the frozen theorem statements. Run #135 reached `MixedSpiderBias.lean`; its two reported errors were repaired in `0d7827002876d0b149c55a136a263254163fc967`.

## Exact first action next session

1. Check PR #4 and the newest GitHub Actions run for the handover head.
2. If the run fails, read the **first failing Lean module/error only** and continue the narrow integration repair from there; do not reopen B1/B2/B3 mathematically.
3. If the run is green, inspect the `#print axioms` output for all seven B final theorems and verify that only acceptable standard Lean/Mathlib axioms occur.
4. Then update `CLAIMS.md`, `ROADMAP.md`, `formal/README.md`, `README.md`, and this handover to mark Frozen B / Stage 5 complete, update PR #4 with the final verification record, and merge PR #4 into `main`.
5. Stop after preparing the repository for Stage 6. **Do not begin Palomar registration in that same Stage-5 completion pass unless a new session explicitly starts Stage 6.**

## Pinned environment

- Lean: **4.34.1**
- Toolchain: `leanprover/lean4:v4.34.1`
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612`
- Dependency lock: `lake-manifest.json`
- CI: `.github/workflows/lean.yml`

Do not casually change these versions.
