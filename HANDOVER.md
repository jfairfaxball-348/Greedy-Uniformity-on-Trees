# Stage-5 continuation handover — Frozen Theorem B next

**Date:** 2026-09-29  
**Completed:** Stages 1–4; Stage-5 finite-law bridge; **Frozen Theorem A**  
**Current stage:** Stage 5 — Lean formalisation, **IN PROGRESS**  
**Checkpoint reached:** checkpoint 3 — Frozen Theorem A complete and verified  
**Working branch for completed A:** `stage5-theorem-a`  
**PR:** #3, `Stage 5: formalise Frozen Theorem A`  
**Verified proof head before documentation updates:** `4c11ed74a25195d8dbe32f09b5fdeb89692e3977`  
**Do not begin:** Stages 6–8

The Stage-4 verdict remains **PASS — FREEZE FOR FORMALISATION**. The frozen theorem package is unchanged. Theorem A is now Lean-verified exactly as audited; Theorem B remains the next and only mathematical target for Stage 5.

## Verified environment

- Lean: **4.34.1**
- Toolchain: `leanprover/lean4:v4.34.1`
- Mathlib: **d13f23b723b8a846827a245b89c10fc7d3f11612**
- Dependency lock: `lake-manifest.json`
- CI: `.github/workflows/lean.yml`

Do not casually change these versions.

## Frozen A — completed

The exact finite permutation-law bridge remains in `GreedyUniformity/Bridge.lean`, including:

    vertexOrders_card
    priorityCertificate_iff_greedyOutput_eq
    fibre_nonempty_of_maximal
    sum_fibreCount_eq_vertexOrders_card
    uniformFibres_iff_greedyLawEqUniform
    bias_eq_zero_iff_greedyLawEqUniform

Theorem A is now completed through the following layers:

- `Counting.lean`: generic factor-two maximal-independent-set count;
- `Pendant.lean`: pendant support decomposition;
- `Marginal.lean`: marginal counting inequality;
- `OrderCount.lean`: exact one-third first-of-three count;
- `MultiLeaf.lean`: `not_uniformFibres_of_two_pendantLeaves`;
- `OneLeaf.lean`: finite swap-fibre proof for the exactly-one-pendant-leaf case, culminating in `not_uniformFibres_of_one_pendantLeaf`;
- `TreeA.lean`: diameter-end structure plus `tree_not_uniformFibres_of_three_le_card`;
- `TheoremA.lean`: direct one/two-vertex cases, graph-isomorphism packaging, and final frozen theorem.

The exact final statements are:

    tree_greedyLawEqUniform_iff_isK1OrK2
    tree_bias_eq_zero_iff_isK1OrK2

with

    IsK1OrK2 G

defined as graph-isomorphism to the complete graph on `Fin 1` or `Fin 2`.

The one-leaf proof is purely finite. It uses `Equiv.swap x y`, priority certificates, injections between permutation fibres, and explicit target orders outside the image to obtain strict fibre inequalities. The Stage-3 continuous-priority integral is not needed in the final Lean proof.

## Verification

GitHub Actions run **#84** on verified proof head

    4c11ed74a25195d8dbe32f09b5fdeb89692e3977

passed all required checks:

- `lake build`;
- forbidden-placeholder rejection;
- `python -m pytest -q` — **4 passed**.

`GreedyUniformity/AxiomCheck.lean` contains:

    #print axioms GreedyUniformity.tree_greedyLawEqUniform_iff_isK1OrK2
    #print axioms GreedyUniformity.tree_bias_eq_zero_iff_isK1OrK2

and run #84 reports, for both:

    [propext, Classical.choice, Quot.sound]

There are no project-specific mathematical axioms, no `sorry`, no `admit`, and no `native_decide` in the final A proof chain.

## Next session: Frozen Theorem B only

Do not redo A or the bridge except for a narrowly targeted compatibility fix genuinely required by B.

Read first:

- `CLAIMS.md`;
- `ROADMAP.md`;
- `proof/INFORMAL_PROOF.md`, especially the mixed-spider section;
- `formal/README.md`;
- `GreedyUniformity/Model.lean`;
- `GreedyUniformity/Bridge.lean`;
- `GreedyUniformity/TheoremA.lean`;
- `GreedyUniformity/AxiomCheck.lean`;
- `HANDOVER.md`.

Formalise exactly the frozen B package:

1. Define the mixed spider `T_{k,l}` in a clean finite Lean representation.
2. Prove the maximal-independent-set classification and count (2^k+1).
3. Formalise the exact centre probability
   [
   p_c=2^{-k}\sum_{j=0}^k\binom{k}{j}\frac1{l+2j+1}.
   ]
4. Formalise the probability of each particular type-(j) non-centre maximal set
   [
   q_j=\frac{l+2j}{2^k(l+2j+1)}.
   ]
5. Under (l=2^k-k), prove the exact bias identity used in Stage 3, positivity, and
   [
   b(T)=O(\sqrt{k}/4^k)
   =O(\sqrt{\log n_k}/n_k^2),
   \qquad n_k=2^k+k+1.
   ]
6. Inspect the final B theorem axioms.
7. Run the complete A+B build, placeholder rejection, and Python regression suite.
8. Only then mark Stage 5 complete.

## Integrity constraints for B

Keep the Stage-4 theorem package frozen. Do not introduce:

- an all-(n) extremal claim;
- optimality or minimizer claims for the mixed spiders;
- matching lower bounds for (a_n);
- “uniform greedy law implies well-covered”;
- worldwide-priority certainty.

The novelty classification remains **plausibly new with bounded uncertainty**.

If B formalisation exposes a genuine mathematical discrepancy rather than a Lean-engineering issue, document it explicitly in the proof/claim ledger. Do not patch around it.

## Workflow boundary

Stages 6–8 have not begun. Do not start Palomar registration, paper writing, or arXiv submission until Frozen B is also soundly formalised and the final combined Stage-5 audit is green.
