# Lean formalisation status

**Stage:** 5 of 8 — IN PROGRESS  
**Checkpoint:** 2 — exact finite permutation-law bridge  
**Date:** 2026-09-29

This directory documents the formalisation boundary. It does not mark Stage 5 complete.

## Pinned environment

- Lean: `4.34.1` (`leanprover/lean4:v4.34.1`)
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612` (tag `v4.34.1`)
- Exact dependency lock: `lake-manifest.json`

Build with:

    lake build

Run the computational regression suite with:

    python -m pytest -q

The GitHub Actions workflow `.github/workflows/lean.yml` builds the root library, rejects `sorry`, `admit`, and `native_decide` in project Lean sources, and runs the Python tests.

## Formal representation

The random scan order is a duplicate-free list that is a permutation of `Finset.univ.toList`. The finite sample space is `vertexOrders`.

For a finite simple graph `G`:

- `greedyStep`, `greedyScan`, and `greedyOutput` implement deterministic random-order greedy MIS;
- `IsMaximalIndependent` is independence plus domination;
- `fibre G I` is the exact set of complete vertex orders whose output is `I`;
- `fibreCount G I` is its cardinality;
- `greedyProb G I` is the exact rational fibre probability;
- `uniformProb G I` is the rational uniform maximal-independent-set probability;
- `GreedyLawEqUniform G` is pointwise equality of the two complete output laws;
- `bias G` is the exact rational total-variation expression;
- `PriorityCertificate G I l` is the finite earlier-selected-neighbour certificate.

This is an exact finite combinatorial model of the frozen uniformly random vertex-permutation process. Python experiments are not used as proof.

## Proved before this checkpoint

`GreedyUniformity/Basic.lean` supplies the deterministic foundation. Its central theorem is:

    GreedyUniformity.greedyOutput_maximal

Every complete vertex order produces an inclusion-maximal independent set. Supporting results establish accumulator monotonicity, preservation of independence, domination after scanning, basic fibre membership, and empty fibres for non-maximal targets.

## Proved at checkpoint 2

`GreedyUniformity/Bridge.lean` completes the exact finite-law bridge. Important theorems include:

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

In particular:

1. `|vertexOrders| = (Fintype.card V)!`;
2. for a complete order, the finite priority certificate is equivalent to being the deterministic greedy output;
3. every maximal independent set has a nonempty, hence positive-cardinality, permutation fibre, using the order with all target vertices before all outside vertices;
4. constant maximal-independent-set fibre sizes are equivalent to equality of the exact greedy law and the uniform maximal-independent-set law;
5. zero exact total-variation bias is equivalent to equality of those laws.

Thus the implemented finite fibres are now connected by proved theorems—not only definitions—to the frozen random-permutation law.

## Verification at checkpoint 2

The root library imports `GreedyUniformity.Bridge`. GitHub Actions run #43 passed:

- `lake build`;
- the forbidden-placeholder check;
- `python -m pytest -q`, with `4 passed`.

No Lean/Mathlib version was changed.

## Not yet proved

Checkpoint 2 does **not** claim either frozen main theorem is formalised. Remaining Stage-5 work is:

1. formalise the structural tree lemmas and Frozen Theorem A;
2. formalise the mixed-spider maximal sets, exact probabilities, tuned bias identity, positivity, and asymptotic bounds for Frozen Theorem B;
3. inspect and accurately record the axioms of the final A/B theorems.

No project-specific axiom, `sorry`, `admit`, or `native_decide` is permitted in the final proof chain.

## Workflow boundary

Do not begin Palomar registration (Stage 6), paper writing (Stage 7), or arXiv submission (Stage 8) until the full frozen A+B package passes Lean and Stage 5 is explicitly marked complete.
