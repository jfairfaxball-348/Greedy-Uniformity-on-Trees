# Lean formalisation status

**Stage:** 5 of 8 — IN PROGRESS  
**Checkpoint:** 1 — finite greedy-order foundation  
**Date:** 2026-09-29

This directory documents the formalisation boundary. It does not mark Stage 5 complete.

## Pinned environment

- Lean: `4.34.1` (`leanprover/lean4:v4.34.1`)
- Mathlib: `d13f23b723b8a846827a245b89c10fc7d3f11612` (tag `v4.34.1`)
- Exact dependency lock: `lake-manifest.json`

Build with:

    lake build

Run the pre-existing computational regression suite with:

    python -m pytest -q

The GitHub Actions workflow `.github/workflows/lean.yml` runs the Lean build, rejects `sorry`, `admit`, and `native_decide` in project Lean sources, and runs the Python tests.

## Formal representation chosen

The random scan order is represented by a duplicate-free list obtained as a permutation of `Finset.univ.toList`. The sample space is `vertexOrders`.

For a finite simple graph `G`:

- `greedyStep`, `greedyScan`, and `greedyOutput` implement the deterministic greedy MIS algorithm;
- `IsMaximalIndependent` is independence plus domination;
- `fibre G I` is the exact finite set of full vertex orders whose greedy output is `I`;
- `fibreCount G I` is its cardinality;
- `greedyProb G I` is the rational fibre probability;
- `uniformProb G I` is the rational uniform maximal-independent-set probability;
- `GreedyLawEqUniform G` is pointwise equality of those complete output laws;
- `bias G` is the exact rational total-variation expression.

This is an exact finite combinatorial model of the frozen random-permutation process; it does not use the Python experiments as proof.

## Proved at checkpoint 1

`GreedyUniformity/Basic.lean` proves the deterministic foundation, including monotonicity of the selected accumulator, preservation of independence, domination of every scanned rejected vertex, and:

    GreedyUniformity.greedyOutput_maximal

which states that every complete vertex order produces an inclusion-maximal independent set.

It also provides basic fibre membership and the fact that a non-maximal target has empty greedy fibre.

## Not yet proved

Checkpoint 1 does **not** claim either frozen main theorem is formalised. Remaining Stage-5 work includes:

1. prove the exact order-space cardinality `|vertexOrders| = |V|!`;
2. prove the finite priority-certificate equivalence with `greedyOutput`;
3. prove the exact bridge between `UniformFibres`, `GreedyLawEqUniform`, and zero `bias`;
4. formalise the structural tree lemmas and Frozen Theorem A;
5. formalise the mixed-spider maximal sets, exact probabilities, tuned bias identity, positivity and asymptotic bounds for Frozen Theorem B;
6. inspect and record axioms of the final main theorems.

No project-specific axiom, `sorry`, `admit`, or `native_decide` is permitted in the final proof chain.

## Workflow boundary

Do not begin Palomar registration (Stage 6), paper writing (Stage 7), or arXiv submission (Stage 8) until the full frozen A+B package passes Lean and Stage 5 is explicitly marked complete.
