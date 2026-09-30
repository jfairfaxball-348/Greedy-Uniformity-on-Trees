# Lean formalisation status

**Stage:** 5 of 8 — COMPLETE  
**Checkpoint:** 4 — Frozen A+B package verified  
**Date:** 2026-09-30

Stage 5 is complete. Frozen Theorems A and B are formalised in the pinned Lean environment and verified by the combined root build.

## Pinned environment

- Lean: `4.34.1` (`leanprover/lean4:v4.34.1`)
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612` (tag `v4.34.1`)
- Exact dependency lock: `lake-manifest.json`

Build with:

    lake build

Run the computational regression suite with:

    python -m pytest -q

The GitHub Actions workflow `.github/workflows/lean.yml` builds the root library, rejects `sorry`, `admit`, and `native_decide` in project Lean sources, and runs the Python tests.

## Exact finite model and bridge

The finite sample space is `vertexOrders`, the complete duplicate-free vertex orders. The core model defines `greedyOutput`, exact permutation fibres and `fibreCount`, `greedyProb`, `uniformProb`, `GreedyLawEqUniform`, and exact rational total-variation `bias`.

`GreedyUniformity/Bridge.lean` proves, among other results,

    vertexOrders_card
    priorityCertificate_iff_greedyOutput_eq
    fibre_nonempty_of_maximal
    sum_fibreCount_eq_vertexOrders_card
    uniformFibres_iff_greedyLawEqUniform
    bias_eq_zero_iff_greedyLawEqUniform

Thus the finite fibre model is connected directly to the frozen random-permutation law and zero-bias formulation.

## Frozen Theorem A — formalised

The structural proof is split across `Counting.lean`, `Pendant.lean`, `Marginal.lean`, `OrderCount.lean`, `MultiLeaf.lean`, `OneLeaf.lean`, `TreeA.lean`, and `TheoremA.lean`.

The final frozen A statements are:

    GreedyUniformity.tree_greedyLawEqUniform_iff_isK1OrK2
    GreedyUniformity.tree_bias_eq_zero_iff_isK1OrK2

where `IsK1OrK2 G` means that `G` is graph-isomorphic to `K₁` or `K₂`. No bounded-size weakening or subclass restriction is used.

## Frozen Theorem B — formalised

The mixed-spider development is split across the `MixedSpider*` modules, `FirstInFinset.lean`, and `TheoremB.lean`. The final frozen B checkpoints are:

    GreedyUniformity.mixedSpider_maximalIndependentSets_card
    GreedyUniformity.greedyProb_mixedSpiderCenter
    GreedyUniformity.greedyProb_mixedSpiderNoncenter
    GreedyUniformity.bias_mixedSpider_tuned_eq_expectation
    GreedyUniformity.bias_mixedSpider_tuned_pos
    GreedyUniformity.bias_mixedSpider_tuned_isBigO
    GreedyUniformity.bias_mixedSpider_tuned_isBigO_sqrt_log_order_div_order_sq

They formalise exactly the frozen B1–B3 package: the `2^k+1` maximal-independent-set count, the exact centre/non-centre permutation-law probabilities, the tuned exact expectation identity and positive bias, and the two requested Big-O conclusions. No all-\(n\), minimizer, optimality, matching-lower-bound, or worldwide-priority statement is introduced.

## Final Stage-5 verification

GitHub Actions run **#161** at verified A+B code head

    47802b8a18a92847e447e88c02ecb42620b3da09

passed:

- the complete root `lake build` — **8954 jobs**;
- forbidden-placeholder rejection for `sorry`, `admit`, and `native_decide`;
- `python -m pytest -q` — **5 passed**.

`GreedyUniformity/AxiomCheck.lean` prints the axioms of both final A theorems and all seven final B checkpoints. Every one reports exactly:

    [propext, Classical.choice, Quot.sound]

There are no project-specific mathematical axioms in the final A+B theorem package.

## Workflow boundary

Stage 5 is complete. Stage 6 (Palomar registration) is next but has not begun. Paper writing (Stage 7) and arXiv submission (Stage 8) have not begun.
