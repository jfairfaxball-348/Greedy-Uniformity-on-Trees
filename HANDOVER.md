# Stage-5 continuation handover

**Date:** 2026-09-29  
**Completed:** Stages 1–4  
**Current stage:** Stage 5 — Lean formalisation, **IN PROGRESS**  
**Checkpoint reached:** finite greedy-order foundation  
**Do not begin:** Stages 6–8

The Stage-4 verdict remains **PASS — FREEZE FOR FORMALISATION**. Frozen Theorems A and B remain exactly the statements recorded in `CLAIMS.md` and `proof/INFORMAL_PROOF.md`; neither has been weakened, strengthened, or replaced.

## Environment pinned in this checkpoint

- Lean: **4.34.1**
- Toolchain file: `leanprover/lean4:v4.34.1`
- Mathlib: **d13f23b723b8a846827a245b89c10fc7d3f11612** (tag `v4.34.1`)
- Dependency lock: `lake-manifest.json`
- Lake project: `lakefile.lean`
- CI: `.github/workflows/lean.yml`

Build command:

    lake build

Python regression command:

    python -m pytest -q

## Formal source added

- `GreedyUniformity/Model.lean`
- `GreedyUniformity/Basic.lean`
- `GreedyUniformity.lean`
- `formal/README.md`

The chosen exact finite representation uses full vertex-order lists:

- `vertexOrders`: permutations of `Finset.univ.toList`;
- `greedyStep`, `greedyScan`, `greedyOutput`: deterministic random-order greedy algorithm;
- `IsMaximalIndependent`: independence plus domination;
- `fibre G I`, `fibreCount G I`: exact permutation fibre and cardinality;
- `greedyProb G I`: rational fibre probability;
- `uniformProb G I`: rational uniform maximal-independent-set probability;
- `GreedyLawEqUniform G`: equality of complete output laws;
- `bias G`: exact rational total-variation expression;
- `PriorityCertificate`: finite earlier-neighbour certificate, defined but not yet proved equivalent to the greedy fibre.

The representation is intended to avoid measure theory while remaining exactly equivalent to the frozen uniformly random permutation model.

## Formal theorem proved at this checkpoint

The central completed foundational theorem is:

    GreedyUniformity.greedyOutput_maximal

For every complete vertex order, the deterministic greedy output is an inclusion-maximal independent set.

Supporting lemmas in `GreedyUniformity/Basic.lean` establish accumulator monotonicity, preservation of independence, domination after scanning, basic fibre membership, and empty fibres for non-maximal targets.

This is background/foundation only. It is not Frozen Theorem A.

## Frozen main-theorem status

- **Frozen Theorem A:** NOT YET fully formalised.
- **Frozen Theorem B:** NOT YET fully formalised.
- **Permutation-fibre / probability equivalence:** partially represented by definitions, but the required theorem bridge is NOT YET complete.
- **Axiom inspection of final A/B:** NOT YET applicable because A/B are not yet proved.

Stage 5 therefore remains **IN PROGRESS**. The project is **not ready for Stage 6**.

## Recommended next Stage-5 slice

Do not redo Stages 1–4 and do not redesign the model unless compilation exposes a genuine flaw.

First complete the finite-order bridge:

1. prove `(vertexOrders (V := V)).card = Nat.factorial (Fintype.card V)`;
2. prove `PriorityCertificate G I l ↔ (IsVertexOrder l ∧ greedyOutput G l = I)` for maximal independent `I`, or an equivalent exact certificate theorem;
3. prove positivity/nonemptiness of every maximal-independent-set fibre (e.g. all target vertices before all outside vertices);
4. prove `UniformFibres G ↔ GreedyLawEqUniform G` on finite nonempty graphs and the corresponding `bias G = 0` bridge;
5. formalise any first-vertex/fibre recurrence that materially helps Theorem A.

Then formalise **Frozen Theorem A** using the Stage-3 diameter-end proof. It is acceptable to replace the iid-integral proof of the one-pendant-leaf comparison by a finite permutation-fibre injection or involution if the conclusion is exactly the same strict paired-set imbalance.

If Theorem A consumes the next full session, stop at another clean Stage-5 checkpoint rather than rushing Frozen Theorem B. A later Stage-5 slice can formalise the mixed-spider family and asymptotics.

## Integrity constraints

- no `sorry`;
- no `admit`;
- no project-specific axioms standing in for mathematics;
- no `native_decide` in the final proof chain;
- no Python experiment used as theorem proof;
- no implication “uniform greedy law implies well-covered” introduced as a lemma or axiom;
- no all-(n), optimality, minimizer, or matching-lower-bound claims added to Frozen B.

If Lean exposes a genuine mathematical gap, update the informal proof and claim ledger honestly instead of hiding it.

## Frozen mathematics and audit boundary

Read before continuing:

- `proof/INFORMAL_PROOF.md`
- `CLAIMS.md`
- `formal/README.md`
- `audit/PRIOR_ART_NOVELTY_AUDIT.md`
- `audit/SEARCH_LOG.md`

The novelty audit is finished for this workflow. Do not reopen broad prior-art searching during Stage 5 unless a formalisation issue reveals an actual mathematical discrepancy.

## Stage-5 completion criterion remains unchanged

Stage 5 is complete only when Frozen A **and** Frozen B are soundly formalised, the exact finite-law bridge is proved, the build and tests pass reproducibly, no forbidden placeholders remain, and final theorem axiom inspection is recorded. Only then proceed to Stage 6.
