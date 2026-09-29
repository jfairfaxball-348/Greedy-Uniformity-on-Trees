# Lean formalisation status

**Stage:** 5 of 8 — IN PROGRESS  
**Checkpoint:** 3 — Frozen Theorem A complete  
**Date:** 2026-09-29

This directory documents the formalisation boundary. Stage 5 is not complete because Frozen Theorem B remains to be formalised.

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

`GreedyUniformity/Bridge.lean` proves, among other results,

    vertexOrders_card
    priorityCertificate_iff_greedyOutput_eq
    fibre_nonempty_of_maximal
    sum_fibreCount_eq_vertexOrders_card
    uniformFibres_iff_greedyLawEqUniform
    bias_eq_zero_iff_greedyLawEqUniform

Thus the finite fibre model is proved equivalent to the frozen random-permutation law and zero-bias formulation.

## Frozen Theorem A — formalised

The structural proof is split across:

- `Counting.lean`: the factor-two maximal-independent-set counting bound;
- `Pendant.lean`: support-vertex decomposition;
- `Marginal.lean`: uniform-fibre-to-marginal inequality;
- `OrderCount.lean`: exact one-third first-of-three counting;
- `MultiLeaf.lean`: the two-or-more-pendant-leaf obstruction;
- `OneLeaf.lean`: the exactly-one-pendant-leaf obstruction via finite permutation-fibre swaps and explicit missed target orders;
- `TreeA.lean`: the diameter-end structure and the all-trees-on-at-least-three-vertices obstruction;
- `TheoremA.lean`: the one/two-vertex base cases and the exact graph-isomorphism statement.

The final frozen statements are:

    GreedyUniformity.tree_greedyLawEqUniform_iff_isK1OrK2
    GreedyUniformity.tree_bias_eq_zero_iff_isK1OrK2

where `IsK1OrK2 G` means that `G` is graph-isomorphic to the complete graph on one or two vertices, i.e. `K₁` or `K₂`.

No bounded-size weakening or subclass restriction is used.

## Verification of checkpoint 3

GitHub Actions run **#84** at verified proof head `4c11ed74a25195d8dbe32f09b5fdeb89692e3977` passed:

- `lake build`;
- forbidden-placeholder rejection;
- `python -m pytest -q` — **4 passed**.

`GreedyUniformity/AxiomCheck.lean` prints the axioms of both final A theorems. The run reports exactly:

    [propext, Classical.choice, Quot.sound]

for each theorem. There are no project-specific mathematical axioms, and the proof chain contains no `sorry`, `admit`, or `native_decide`.

## Remaining Stage-5 work

Frozen Theorem B remains untouched in this checkpoint. The next session should formalise exactly the audited mixed-spider package B1–B3, without adding all-`n`, minimizer, optimality, matching-lower-bound, or worldwide-priority claims.

After B is complete, run the final combined A+B build, placeholder rejection, Python regressions, and theorem axiom inspection before marking Stage 5 complete.

## Workflow boundary

Do not begin Palomar registration (Stage 6), paper writing (Stage 7), or arXiv submission (Stage 8) until Frozen A and B are both soundly formalised and Stage 5 is explicitly complete.
