# Stage-5 continuation handover

**Date:** 2026-09-29  
**Completed:** Stages 1–4  
**Current stage:** Stage 5 — Lean formalisation, **IN PROGRESS**  
**Checkpoint reached:** partial checkpoint 3 — Frozen Theorem A structural/counting layer  
**Working branch:** `stage5-theorem-a`  
**Open PR:** #3, `Stage 5: formalise Frozen Theorem A`  
**Pre-handover code head:** `2c3b79d6d672def2fa9b5f1c70ab2a57a2772cce`  
**Do not begin:** Stages 6–8

The Stage-4 verdict remains **PASS — FREEZE FOR FORMALISATION**. Frozen Theorems A and B remain exactly the statements recorded in `CLAIMS.md` and `proof/INFORMAL_PROOF.md`.

## Pinned environment

- Lean: **4.34.1**
- Toolchain: `leanprover/lean4:v4.34.1`
- Mathlib: **d13f23b723b8a846827a245b89c10fc7d3f11612**
- Dependency lock: `lake-manifest.json`
- CI: `.github/workflows/lean.yml`

Do not casually change these versions.

## Formal source now relevant

- `GreedyUniformity/Model.lean`
- `GreedyUniformity/Basic.lean`
- `GreedyUniformity/Bridge.lean`
- `GreedyUniformity/Counting.lean`
- `GreedyUniformity/Pendant.lean`
- `GreedyUniformity/Marginal.lean`
- `GreedyUniformity/OrderCount.lean`
- `GreedyUniformity/MultiLeaf.lean`
- `GreedyUniformity/OneLeaf.lean`
- `GreedyUniformity/TreeA.lean`
- `GreedyUniformity.lean`

## Previously completed bridge

The exact finite permutation-law bridge remains complete. Key theorems include:

    vertexOrders_card
    priorityCertificate_iff_greedyOutput_eq
    fibre_nonempty_of_maximal
    sum_fibreCount_eq_vertexOrders_card
    uniformFibres_iff_greedyLawEqUniform
    bias_eq_zero_iff_greedyLawEqUniform

## New Stage-5 progress in this slice

The branch now contains the main structural/counting machinery for Frozen Theorem A.

### Generic counting layer

`GreedyUniformity/Counting.lean` proves, among other helpers,

    maximalIndependentSetsOn_card_le_two_mul_erase

formalising the factor-two maximal-independent-set counting bound needed by the pendant argument.

### Pendant decomposition

`GreedyUniformity/Pendant.lean` formalises the support-vertex decomposition and proves the corresponding containing/excluding maximal-independent-set counts, including

    maximalIndependentSetsExcluding_card_le_two_mul_containing

### Marginal bridge

`GreedyUniformity/Marginal.lean` relates orders selecting a vertex to sums of greedy fibres and proves

    uniformFibres_implies_vertexOrders_le_three_mul_ordersSelecting

under the factor-two maximal-set count.

### Three-order counting and multiple-leaf obstruction

`GreedyUniformity/OrderCount.lean` now has a simplified finite-order proof that one of three distinct vertices is first with exactly one-third of the complete orders.

`GreedyUniformity/MultiLeaf.lean` proves the strict multiple-pendant-leaf contradiction, culminating in

    not_uniformFibres_of_two_pendantLeaves

The CI run immediately before the final TreeA API fixes compiled `Counting`, `OrderCount`, `Pendant`, `Marginal`, and `MultiLeaf` successfully. Its only remaining failures were in `TreeA.lean` and were API/cast issues, not mathematical failures.

### Tree structure

`GreedyUniformity/TreeA.lean` contains:

    tree_maximalPath_pendantStar
    tree_exists_pendantStar_of_three_le_card

The two last reported errors in this file were fixed at commit

    679ffafa18f6feff1eacb99328c5198f0fb98aa0

by correcting the extended-natural cardinal cast and the namespace of the longest-path existence theorem.

### One-leaf case: foundation added, strict fibre comparison still missing

`GreedyUniformity/OneLeaf.lean` was added at commit

    51ddafdd74021ec49b49296599fb91b329605acd

and `TreeA.lean` was changed to import it at

    2c3b79d6d672def2fa9b5f1c70ab2a57a2772cce

It currently contains:

    precedes_map_equiv
    pendantLeaves_eq_singleton_of_card_eq_one
    center_insert_maximal_of_maximalOn_pendantF
    leaf_insert_maximal_of_dominates_z
    leaf_z_insert_maximal_of_not_dominates_z

These establish the local paired maximal sets needed for the exactly-one-pendant-leaf case.

At handover time, GitHub Actions run **#65** for code head `2c3b79d6...` was still in progress, so do not assume the new `OneLeaf.lean` foundation is CI-green until checking that run first.

## Recommended next proof route

Continue Frozen Theorem A only.

1. Check Actions run #65 first and repair any Lean-engineering errors in `OneLeaf.lean` or `TreeA.lean`.
2. Finish the exactly-one-pendant-leaf case using a **finite permutation-fibre comparison**, avoiding the Stage-3 continuous integral if possible.
3. The intended route is to swap the labels/positions of the unique leaf `x` and support vertex `y` in complete orders:
   - use `precedes_map_equiv`;
   - use the priority-certificate/output equivalence from `Bridge.lean`;
   - prove an injection from the fibre of the centre-containing paired set into the appropriate leaf-containing paired set;
   - exhibit a target order outside the image to get strict inequality of fibre sizes.
4. Derive `¬ UniformFibres G` for the one-leaf support configuration.
5. Combine it with `not_uniformFibres_of_two_pendantLeaves` and `tree_exists_pendantStar_of_three_le_card` to prove the ≥3-vertex obstruction.
6. Add direct `K₁` and `K₂` base cases.
7. State Frozen Theorem A in both law-equality and zero-bias forms using the completed bridge.
8. Run full CI and inspect axioms before declaring A formalised.

If finishing A consumes the next session, stop there. Do not rush Frozen B.

## Useful recent commits

- `c6d11d9cbe9202151024038cd0f64e981514d6c4` — simplify three-order counting proof.
- `8d2f9e0bb54012623dccbde3a94c24e076c5f423` — repair multi-leaf order witness.
- `679ffafa18f6feff1eacb99328c5198f0fb98aa0` — repair TreeA path/cardinality APIs.
- `51ddafdd74021ec49b49296599fb91b329605acd` — add one-leaf paired-set foundations.
- `2c3b79d6d672def2fa9b5f1c70ab2a57a2772cce` — layer TreeA over OneLeaf.

## Integrity constraints

- no `sorry`;
- no `admit`;
- no project-specific axioms standing in for mathematics;
- no `native_decide` in the final proof chain;
- no Python experiment used as theorem proof;
- do not introduce “uniform greedy law implies well-covered”;
- do not add all-n, optimality, minimizer, matching-lower-bound, or `a_n` claims to Frozen B.

If Lean exposes a genuine mathematical gap, distinguish it from an engineering issue and update the informal proof and claim ledger honestly.

## Workflow boundary

The novelty audit is complete for this workflow. Do not reopen broad prior-art searching unless formalisation exposes an actual mathematical discrepancy. Do not begin Palomar registration, paper writing, or arXiv submission until Frozen A and B are soundly formalised, final theorem axiom inspection is recorded, and Stage 5 is explicitly complete.
