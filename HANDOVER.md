# Stage-5 continuation handover

**Date:** 2026-09-29  
**Completed:** Stages 1–4  
**Current stage:** Stage 5 — Lean formalisation, **IN PROGRESS**  
**Checkpoint reached:** 2 — exact finite permutation-law bridge  
**Do not begin:** Stages 6–8

The Stage-4 verdict remains **PASS — FREEZE FOR FORMALISATION**. Frozen Theorems A and B remain exactly the statements recorded in `CLAIMS.md` and `proof/INFORMAL_PROOF.md`; neither has been weakened, strengthened, or replaced.

## Pinned environment

- Lean: **4.34.1**
- Toolchain: `leanprover/lean4:v4.34.1`
- Mathlib: **d13f23b723b8a846827a245b89c10fc7d3f11612** (tag `v4.34.1`)
- Dependency lock: `lake-manifest.json`
- CI: `.github/workflows/lean.yml`

Do not casually change these versions in the next Stage-5 slice.

## Formal source

- `GreedyUniformity/Model.lean`
- `GreedyUniformity/Basic.lean`
- `GreedyUniformity/Bridge.lean`
- `GreedyUniformity.lean`
- `formal/README.md`

The model uses literal finite vertex-order fibres. `vertexOrders` is the set of permutations of `Finset.univ.toList`; `fibre G I` is the set of complete orders with deterministic output `I`; `greedyProb`, `uniformProb`, `GreedyLawEqUniform`, and `bias` are exact rational finite-law definitions.

## Checkpoint 1 foundation retained

The central deterministic theorem remains:

    GreedyUniformity.greedyOutput_maximal

Every complete vertex order produces an inclusion-maximal independent set.

Do not replace this implementation with a second unrelated greedy model unless a genuine defect is found.

## Checkpoint 2 bridge completed

`GreedyUniformity/Bridge.lean` now proves the exact finite-order/probability bridge. Important theorem names are:

    GreedyUniformity.vertexOrders_card
    GreedyUniformity.greedyOutput_priorityCertificate
    GreedyUniformity.greedyOutput_eq_of_priorityCertificate
    GreedyUniformity.priorityCertificate_iff_greedyOutput_eq
    GreedyUniformity.fibre_nonempty_of_maximal
    GreedyUniformity.fibreCount_pos_of_maximal
    GreedyUniformity.sum_fibreCount_eq_vertexOrders_card
    GreedyUniformity.uniformFibres_iff_greedyLawEqUniform
    GreedyUniformity.greedyLawEqUniform_iff_on_maximal
    GreedyUniformity.bias_eq_zero_iff_greedyLawEqUniform

Consequences now formally established:

1. the complete order sample space has cardinality `|V|!`;
2. for a complete order, the earlier-selected-neighbour `PriorityCertificate` is equivalent to deterministic greedy output;
3. every maximal independent set has positive permutation fibre, by placing all target vertices before all outside vertices;
4. equal maximal-set fibre sizes are equivalent to equality of the exact greedy and uniform laws;
5. zero total-variation bias is equivalent to equality of those laws.

This closes the finite-law bridge requested at the start of checkpoint 2.

## Verification

The root library imports `GreedyUniformity.Bridge`. GitHub Actions run #43 passed:

    lake build
    placeholder rejection
    python -m pytest -q

The Python result was:

    4 passed

There is no `sorry`, `admit`, project-specific mathematical axiom, or `native_decide` in the project Lean proof chain checked by CI.

No genuine mathematical discrepancy was found while formalising the bridge. The fixes required after the first CI pass were Lean-engineering fixes only: finite-set membership projections, list/get-element argument shapes, and simplification normal forms.

## Frozen main-theorem status

- **Finite-order/probability bridge:** COMPLETE.
- **Frozen Theorem A:** NOT YET fully formalised.
- **Frozen Theorem B:** NOT YET fully formalised.
- **Final A/B axiom inspection:** NOT YET applicable.

Stage 5 remains **IN PROGRESS**. The project is **not ready for Stage 6**.

## Recommended next Stage-5 slice: Frozen Theorem A

Do not redo Stages 1–4 and do not redo the finite-law bridge except for a targeted correction genuinely required by A.

Formalise A using the Stage-3 architecture:

1. diameter-end pendant-star structure;
2. the maximal-independent-set counting bound `m(H) ≤ 2 m(H-z)`;
3. the multiple-pendant-leaf greedy-vs-uniform marginal mismatch;
4. the exactly-one-pendant-leaf strict paired-set imbalance;
5. direct `K₁` and `K₂` base cases;
6. conclude both the law-equality and zero-bias formulations using the completed bridge.

For the one-pendant-leaf case, a finite permutation-fibre injection, bijection, or involution may replace the Stage-3 iid-integral argument if it proves exactly the same strict comparison. Do not weaken A to bounded-size trees, paths, spiders, well-covered trees, or an extra-hypothesis subclass.

If A consumes the next full session, stop at a clean third Stage-5 checkpoint rather than rushing Frozen B. A later Stage-5 slice should then concentrate on the mixed-spider family and asymptotics.

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
