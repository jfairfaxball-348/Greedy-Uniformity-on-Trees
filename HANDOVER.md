# Stage-6 Palomar packaging handover — ready for user registration

**Date:** 2026-09-30  
**Completed:** Stages 1–5  
**Current stage:** Stage 6 — Palomar registration, **IN PROGRESS**  
**Repository-side package:** **PREPARED**  
**Dedicated Palomar full preflight:** **PASSED**  
**External Palomar registration:** **NOT YET PERFORMED**  
**Working branch:** `stage6-palomar-preflight`

The Stage-4 novelty classification remains exactly **plausibly new with bounded
uncertainty**. Do not strengthen it to worldwide-priority certainty. No all-(n)
extremal, minimizer, global-optimality, matching-lower-bound, or
“uniform greedy law implies well-covered” claim has been added.

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

Stage 6 did not strengthen or reopen these mathematical statements. The
Palomar-required module/public-visibility port changes repository format only.

## Current Palomar package

- selected project: repository root;
- metadata: `formalization.yaml`;
- Comparator configuration: `comparator.json`;
- Challenge: `GreedyUniformity/PalomarChallenge.lean`;
- Solution: `GreedyUniformity/PalomarSolution.lean`;
- licence: Apache-2.0;
- compared theorems: all two final A declarations plus all seven final B
  checkpoints;
- permitted axioms: `propext`, `Classical.choice`, `Quot.sound`;
- single Comparator definition hole:
  `GreedyUniformity.mixedSpiderNoncenterSet`.

The Challenge gives the intended finite-set definition of
`mixedSpiderNoncenterSet` explicitly. Separate Challenge/Solution compilation
produced non-identical elaborated bodies for that one definition, so the
Palomar-supported `definition_names` mechanism is used narrowly. Comparator
still checks its type and safety, the verifier checks the Solution-side body for
permitted axioms, and all nine theorem statements are compared exactly.

## Palomar-forced environment migration

Stage 5 was verified under Lean 4.34.1 and Mathlib
`d13f23b723b8a846827a245b89c10fc7d3f11612`.

Current PalomarSubmission commit
`65f0154ed776cd26c224254aa57b379137f28b0d` requires the Lean module system
and a toolchain at or above v4.35.0-rc2. Stage 6 therefore moved the repository
to:

- Lean: **4.35.0-rc3**
- toolchain: `leanprover/lean4:v4.35.0-rc3`
- Mathlib: `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`)
- exact dependency lock: `lake-manifest.json`

This was a packaging compatibility correction required by current Palomar
policy, not a mathematical change.

## Mechanical preflight record

The reusable workflow is pinned to PalomarSubmission commit
`65f0154ed776cd26c224254aa57b379137f28b0d`, with:

- `mode: full`;
- `execution_profile: palomar-standard-v1`;
- explicit `comparator_config_path: comparator.json`.

A full predictive preflight passed on package commit
`6f4e72ba8d01a34310eb40710c0557f507aea392` in workflow run #7
(GitHub Actions run id `36718192673`). Its mechanical report had:

- status: `pass`;
- stage: `complete`;
- warnings: none;
- errors: none;
- Challenge trust level: `high`;
- con-ron: accepted;
- NanoDa: accepted;
- Lean default kernel: accepted.

That pass is the substantive package checkpoint before the final documentation
batch. The final registration commit is re-run through the same full preflight
after this handover update; use the exact final green commit reported at the end
of the Stage-6 session.

## What remains for the responsible user

Do **not** begin Stage 7 yet. To complete Stage 6, the responsible user must:

1. open the Palomar submission interface and authenticate through the browser;
2. submit repository `jfairfaxball-348/Greedy-Uniformity-on-Trees`;
3. use the exact 40-character commit SHA from the final green full preflight;
4. select the repository root as the project;
5. use `comparator.json` as the Comparator configuration path;
6. use the default `formalization.yaml` metadata path;
7. leave existing Palomar ID blank for a new registration;
8. personally confirm the “responsible author or maintainer” relationship only
   if that statement is true;
9. review the Apache-2.0 licence choice and the human/AI-production metadata;
10. submit and record the resulting Palomar identifier.

Until step 10 has actually occurred, the correct status is **package prepared,
preflight passed, ready for user registration — not registered**.

Stage 7 (paper writing) and Stage 8 (arXiv submission) remain blocked until
Palomar registration is actually complete.
