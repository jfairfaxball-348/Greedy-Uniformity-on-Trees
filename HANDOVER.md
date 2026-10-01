# Stage-6 completion handover — ready for Stage 7

**Date:** 2026-10-01  
**Completed:** Stages 1–6  
**Current status:** Stage 6 — Palomar registration, **COMPLETE**  
**Next stage:** Stage 7 — research paper, **NOT STARTED**  
**Palomar ID:** `PALOMAR-2026-10-01-000003`  
**Palomar version:** 1  
**Palomar trust:** high  
**Registered source commit:** `1733c29a5165148d71a2f0bd1ed2dcd7c35309ce`  
**Stage-6 package merge:** PR #5 → `main`, merge commit `2ef08c9d964dffb66c314930a3b89bbc28b33999`

The Stage-4 novelty classification remains exactly **plausibly new with bounded
uncertainty**. Do not strengthen it to worldwide-priority certainty. No all-(n)
extremal, minimizer, global-optimality, matching-lower-bound, or
“uniform greedy law implies well-covered” claim has been added.

## Palomar registration record

The corrected Stage-6 package was accepted into the public Palomar registry as:

    PALOMAR-2026-10-01-000003

version 1, published at `2026-10-01T00:28:54Z`, with status `registered` and
trust level `high`.

Public entry:

    https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-01-000003&version=1

Palomar preserved the exact registered source commit

    1733c29a5165148d71a2f0bd1ed2dcd7c35309ce

under:

    PalomarArchive/jfairfaxball-348--Greedy-Uniformity-on-Trees--0c04ff5c5faa

The registry lists all nine intended theorem declarations: the two final
Theorem A declarations and all seven final Theorem B checkpoints.

## Frozen theorem boundary

The final Theorem A declarations remain:

    GreedyUniformity.tree_greedyLawEqUniform_iff_isK1OrK2
    GreedyUniformity.tree_bias_eq_zero_iff_isK1OrK2

The final Theorem B checkpoints remain:

    GreedyUniformity.mixedSpider_maximalIndependentSets_card
    GreedyUniformity.greedyProb_mixedSpiderCenter
    GreedyUniformity.greedyProb_mixedSpiderNoncenter
    GreedyUniformity.bias_mixedSpider_tuned_eq_expectation
    GreedyUniformity.bias_mixedSpider_tuned_pos
    GreedyUniformity.bias_mixedSpider_tuned_isBigO
    GreedyUniformity.bias_mixedSpider_tuned_isBigO_sqrt_log_order_div_order_sq

Stage 6 did not strengthen or reopen these mathematical statements.

## Palomar package and environment

The registered package uses:

- repository root as the selected project;
- `formalization.yaml`;
- `comparator.json`;
- `GreedyUniformity/PalomarChallenge.lean`;
- `GreedyUniformity/PalomarSolution.lean`;
- Apache-2.0;
- permitted axioms `propext`, `Classical.choice`, and `Quot.sound`.

Current Palomar policy required the packaging-only migration to:

- Lean **4.35.0-rc3**;
- toolchain `leanprover/lean4:v4.35.0-rc3`;
- Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e`.

The Stage-5 mathematical package had already been verified under Lean 4.34.1 /
Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. The Stage-6 migration was
for Palomar compatibility, not a change of theorem scope.

## Review correction incorporated before registration

The first browser submission at commit
`ed5d05baf8850226e7de21c7350dccb21f909d43` passed mechanical verification
but received an editorial request to align the detailed one-pendant-leaf
informal proof with the strict permutation-fibre injection used by Lean.

That documentation correction was made before the successful registration.
The theorem statements and Lean proofs were not changed.

## Stage-7 boundary

Stage 7 may now begin. The paper must be written from the frozen, audited,
formalised, and Palomar-registered theorem package. In particular:

- preserve the exact A+B theorem scope;
- preserve the novelty wording **plausibly new with bounded uncertainty**;
- clearly separate standard/background ingredients from contribution-level
  claims;
- state the exact greedy-permutation model and total-variation bias definition;
- present the structural proof of Theorem A and the mixed-spider calculations
  of Theorem B;
- accurately describe the Lean formalisation and Palomar registration;
- do not add an all-n extremal, optimality, matching-lower-bound,
  well-covered-converse, or worldwide-priority claim without a new proof and
  audit.

Stage 8 (arXiv submission) remains blocked until the Stage-7 paper is complete.
