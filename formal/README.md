# Lean formalisation status

**Stage 5 theorem formalisation:** COMPLETE  
**Stage 6 Palomar registration:** COMPLETE — `PALOMAR-2026-10-01-000003`, version 1, high trust  
**Publication status:** `arXiv:2610.02276` v1 is live  
**Status refreshed:** 2026-10-05

Frozen Theorems A and B remain fully formalised. Stage 6 made a
Palomar-required module/toolchain compatibility port without strengthening the
frozen theorem statements.

## Environments

### Stage-5 verification baseline

- Lean: `4.34.1` (`leanprover/lean4:v4.34.1`)
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612` (tag `v4.34.1`)
- GitHub Actions run #161 at `47802b8a18a92847e447e88c02ecb42620b3da09`

That run passed the complete A+B root build, forbidden-placeholder rejection,
and the Python regression suite.

### Current Palomar-compatible environment

Current PalomarSubmission policy requires Lean's module system and a toolchain
at or above v4.35.0-rc2. The repository is therefore now pinned to:

- Lean: `4.35.0-rc3` (`leanprover/lean4:v4.35.0-rc3`)
- Mathlib: `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`)
- exact dependency lock: `lake-manifest.json`

Build with:

    lake build

Run the computational regression suite with:

    python -m pytest -q

The ordinary GitHub Actions placeholder audit rejects `sorry`, `admit`, and
`native_decide` in proof-development sources. It excludes only
`GreedyUniformity/PalomarChallenge.lean`, where theorem holes are intentional
and are checked against the proved Solution by Palomar Comparator.

## Exact finite model and bridge

The finite sample space is `vertexOrders`, the complete duplicate-free vertex
orders. The core model defines `greedyOutput`, exact permutation fibres and
`fibreCount`, `greedyProb`, `uniformProb`, `GreedyLawEqUniform`, and exact
rational total-variation `bias`.

`GreedyUniformity/Bridge.lean` proves, among other results,

    vertexOrders_card
    priorityCertificate_iff_greedyOutput_eq
    fibre_nonempty_of_maximal
    sum_fibreCount_eq_vertexOrders_card
    uniformFibres_iff_greedyLawEqUniform
    bias_eq_zero_iff_greedyLawEqUniform

Thus the finite fibre model is connected directly to the frozen
random-permutation law and zero-bias formulation.

## Frozen Theorem A — formalised

The final frozen A statements are:

    GreedyUniformity.tree_greedyLawEqUniform_iff_isK1OrK2
    GreedyUniformity.tree_bias_eq_zero_iff_isK1OrK2

where `IsK1OrK2 G` means that `G` is graph-isomorphic to (K_1) or (K_2).
No bounded-size weakening or subclass restriction is used.

## Frozen Theorem B — formalised

The final frozen B checkpoints are:

    GreedyUniformity.mixedSpider_maximalIndependentSets_card
    GreedyUniformity.greedyProb_mixedSpiderCenter
    GreedyUniformity.greedyProb_mixedSpiderNoncenter
    GreedyUniformity.bias_mixedSpider_tuned_eq_expectation
    GreedyUniformity.bias_mixedSpider_tuned_pos
    GreedyUniformity.bias_mixedSpider_tuned_isBigO
    GreedyUniformity.bias_mixedSpider_tuned_isBigO_sqrt_log_order_div_order_sq

They formalise exactly the frozen B1–B3 package: the (2^k+1)
maximal-independent-set count, the exact centre/non-centre permutation-law
probabilities, the tuned exact expectation identity and positive bias, and the
two stated Big-O conclusions. No all-(n), minimizer, optimality,
matching-lower-bound, or worldwide-priority statement is introduced.

## Axiom boundary

Stage-5 `GreedyUniformity/AxiomCheck.lean` reports exactly

    [propext, Classical.choice, Quot.sound]

for both final A statements and all seven final B checkpoints. There are no
project-specific mathematical axioms in the final A+B theorem package.

## Palomar mechanical verification

The Stage-6 package uses:

- `GreedyUniformity/PalomarChallenge.lean`;
- `GreedyUniformity/PalomarSolution.lean`;
- `comparator.json`;
- `formalization.yaml`;
- Apache-2.0 `LICENSE`.

The dedicated `mode: full` Palomar preflight is pinned to PalomarSubmission
commit `65f0154ed776cd26c224254aa57b379137f28b0d` and
`palomar-standard-v1`. A full pass has confirmed Challenge provenance,
complete Solution build, Comparator success, permitted-axiom enforcement,
con-ron, NanoDa, and Lean default-kernel replay with no warnings or errors.

Comparator uses one narrowly documented `definition_names` entry,
`GreedyUniformity.mixedSpiderNoncenterSet`, because separate Challenge/Solution
compilation gives non-identical elaborated bodies for that definition. The
Challenge states the intended finite-set definition explicitly; Comparator
checks the definition type/safety and Solution-side axiom use, while the nine
frozen theorem statements are compared exactly.

## Workflow completion

Stage 6 is complete: the frozen theorem package is registered with Palomar as
`PALOMAR-2026-10-01-000003`, version 1, high trust, from immutable source
commit `1733c29a5165148d71a2f0bd1ed2dcd7c35309ce`.

Stages 7 and 8 are also complete. The research manuscript is `paper/main.tex`,
and the paper is live as [`arXiv:2610.02276`](https://arxiv.org/abs/2610.02276),
version 1, submitted 2026-10-01, with arXiv-issued DOI
[`10.48550/arXiv.2610.02276`](https://doi.org/10.48550/arXiv.2610.02276).
