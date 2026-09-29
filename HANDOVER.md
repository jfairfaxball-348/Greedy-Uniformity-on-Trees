# Stage-5 continuation handover — Frozen Theorem B next

**Date:** 2026-09-29  
**Completed:** Stages 1–4; Stage-5 finite-law bridge; **Frozen Theorem A formalisation**  
**Current stage:** Stage 5 — Lean formalisation, **IN PROGRESS**  
**Checkpoint reached:** Frozen Theorem A complete  
**A working branch:** `stage5-theorem-a`  
**A integration PR:** #3, `Stage 5: formalise Frozen Theorem A`  
**Verified A theorem/axiom head:** `4c11ed74a25195d8dbe32f09b5fdeb89692e3977`  
**Pre-handover status-doc head:** `271fa199e899261dde8f9a81003200f2850b38ce`  
**Do not begin:** Stages 6–8

The Stage-4 verdict remains **PASS — FREEZE FOR FORMALISATION**. The novelty classification remains **plausibly new with bounded uncertainty**. No claim of worldwide priority has been added.

## Immediate first action next session

1. Check the latest GitHub Actions result on PR #3 / branch `stage5-theorem-a`.
2. If the final handover/status head is green, merge PR #3 into `main`.
3. Create a fresh branch for Frozen Theorem B (recommended: `stage5-theorem-b`).
4. Continue **Stage 5 only** with Frozen B. Do not reopen Frozen A except for a narrowly targeted integration correction genuinely forced by B.

Do not start B on the A branch before integrating the completed A checkpoint.

## Frozen Theorem A — completed

The exact finite permutation-law bridge remains complete in `Bridge.lean`:

    vertexOrders_card
    priorityCertificate_iff_greedyOutput_eq
    fibre_nonempty_of_maximal
    sum_fibreCount_eq_vertexOrders_card
    uniformFibres_iff_greedyLawEqUniform
    bias_eq_zero_iff_greedyLawEqUniform

The structural/counting A chain is complete in:

- `GreedyUniformity/Counting.lean`
- `GreedyUniformity/Pendant.lean`
- `GreedyUniformity/Marginal.lean`
- `GreedyUniformity/OrderCount.lean`
- `GreedyUniformity/MultiLeaf.lean`
- `GreedyUniformity/OneLeaf.lean`
- `GreedyUniformity/TreeA.lean`
- `GreedyUniformity/TheoremA.lean`

Important completed A theorems include:

    not_uniformFibres_of_two_pendantLeaves
    fibreCount_leaf_lt_center_of_dominates_z
    fibreCount_center_lt_leaf_z_of_not_dominates_z
    not_uniformFibres_of_one_pendantLeaf
    tree_exists_pendantStar_of_three_le_card
    tree_not_uniformFibres_of_three_le_card
    uniformFibres_of_card_le_two
    tree_uniformFibres_iff_card_eq_one_or_two
    tree_greedyLawEqUniform_iff_card_eq_one_or_two
    tree_bias_eq_zero_iff_card_eq_one_or_two
    tree_greedyLawEqUniform_iff_isK1OrK2
    tree_bias_eq_zero_iff_isK1OrK2

`IsK1OrK2 G` is the explicit graph-isomorphism formulation: `G` is isomorphic to the complete graph on `Fin 1` or on `Fin 2`.

### One-leaf case

The Stage-3 continuous-priority integral was **not** reproduced. The Lean proof uses a finite permutation-fibre comparison.

For a residual maximal independent set `A`, it builds the paired maximal sets and uses `Equiv.swap x y` on complete orders. The proof transports priority certificates under the swap and gives explicit target orders outside the swap image, yielding strict fibre inequalities in both cases:

- if `A` dominates `z`: leaf fibre < centre fibre;
- if `A` does not dominate `z`: centre fibre < leaf-plus-`z` fibre.

This culminates in:

    not_uniformFibres_of_one_pendantLeaf

There was no mathematical discrepancy exposed by formalisation; the encountered failures were Lean elaboration/API issues and were repaired without changing the theorem.

## Verification of Frozen A

GitHub Actions run **#84** for head

    4c11ed74a25195d8dbe32f09b5fdeb89692e3977

passed:

- `lake build`;
- forbidden-placeholder rejection;
- `python -m pytest -q`, with **4 passed**.

The placeholder check covers `sorry`, `admit`, and `native_decide`.

`GreedyUniformity/AxiomCheck.lean` runs Lean axiom printing on both final A statements. The exact reported dependencies for each are:

    [propext, Classical.choice, Quot.sound]

No project-specific mathematical axiom occurs in the Frozen A proof chain.

## Pinned environment

- Lean: **4.34.1**
- Toolchain: `leanprover/lean4:v4.34.1`
- Mathlib: **d13f23b723b8a846827a245b89c10fc7d3f11612**
- Dependency lock: `lake-manifest.json`
- CI: `.github/workflows/lean.yml`

Do not casually change these versions.

## Main objective next session — Frozen Theorem B only

Formalise exactly the Stage-4-frozen mixed-spider theorem package already recorded in `CLAIMS.md` and `proof/INFORMAL_PROOF.md`.

The frozen content is:

1. For the mixed spider `T_{k,l}`, the number of maximal independent sets is exactly
   [
   2^k+1.
   ]

2. With `N=2^k`, the centre-containing output probability is
   [
   p_c=2^{-k}\sum_{j=0}^k {k\choose j}\frac1{l+2j+1},
   ]
   and each particular type-`j` non-centre maximal independent set has probability
   [
   q_j=\frac{l+2j}{2^k(l+2j+1)}.
   ]

3. Under the tuned choice
   [
   l=2^k-k,
   ]
   prove positive bias and
   [
   b(T)=O(\sqrt{k}/4^k)
        =O(\sqrt{\log n_k}/n_k^2)
   ]
   along
   [
   n_k=2^k+k+1.
   ]

Use the already-formalised finite permutation model where practical. If a rational/probability identity is cleaner via exact finite counting than through continuous priorities, prefer the finite proof.

## Frozen-B integrity constraints

Do **not** introduce or claim:

- “uniform greedy law implies well-covered”;
- an all-(n) extremal theorem;
- optimality or minimizer claims for the mixed spiders;
- a matching lower bound for (a_n);
- worldwide-priority certainty;
- any strengthening beyond the Stage-4-frozen B package.

The novelty verdict remains only **plausibly new with bounded uncertainty**.

If formalisation exposes a genuine mathematical discrepancy, document it explicitly in `proof/INFORMAL_PROOF.md` and `CLAIMS.md` rather than weakening or patching silently.

## Completion requirements for Stage 5

Stage 5 is **not complete** at this handover because Frozen B remains.

Before Stage 5 can be declared complete, Frozen B must also have:

- a passing `lake build`;
- passing placeholder rejection;
- passing Python regression tests;
- no `sorry`;
- no `admit`;
- no project-specific mathematical axioms;
- no `native_decide` in the final proof chain;
- final theorem axiom inspection recorded accurately.

Only after the full frozen A+B package is formalised and verified should Stage 6 (Palomar registration) begin.
