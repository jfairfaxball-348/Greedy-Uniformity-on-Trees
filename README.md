# Greedy Uniformity on Trees

Research repository for the distribution of random greedy maximal independent sets on finite trees.

## Current status

**Stages 1–4 are complete. Stage 5 (Lean formalisation) is IN PROGRESS. Checkpoint 3 includes the pinned Lean/Mathlib environment, the exact finite greedy-order model and law bridge, and a complete Lean formalisation of Frozen Theorem A. Frozen Theorem B remains to be formalised.**

Stage 2 gave PASS FOR PROOF, not a priority certificate. Stage 3 produced the complete informal proof. Stage 4 then re-audited the **actual proved theorem and proof shape** against current primary literature. The final classification is deliberately bounded: both A and B are **plausibly new with bounded uncertainty**, not “definitely novel” or “unique worldwide”.

The closest source remains Kryven–Versendaal–de Vries (arXiv:2608.07239v1). Their Definition 3.6 is the same finite IMIS law, and Proposition 3.8 gives a sufficient exact-uniformity condition (regular independent sets), but the checked paper states no converse. Its Theorem 3.23 classifies the stronger 2-uniform class and therefore does not make the tree obstruction routine.

## Model

Choose a uniformly random permutation of the vertices of a finite nonempty simple undirected tree, scan it once, and select a vertex iff it has no previously selected neighbour. The output is an inclusion-maximal independent set.

For a tree \(T\), let \(G_T\) be the greedy output law and \(U_T\) uniform on its maximal independent sets \(\mathcal M(T)\). Define
\[
b(T)=\frac12\sum_{I\in\mathcal M(T)}
\left|G_T(I)-\frac1{|\mathcal M(T)|}\right|.
\]

## Frozen theorem package for Stage 5

- **A — exact obstruction:** for every finite nonempty tree \(T\),
  \[
  G_T=U_T\iff T\cong K_1\text{ or }K_2,
  \]
  equivalently \(b(T)=0\) iff \(T\cong K_1\) or \(K_2\).

- **B — explicit near-uniform connected trees:** for the mixed spider \(T_{k,l}\), Stage 3 gives exact probabilities \(p_c\) and \(q_j\). Under the tuning \(l=2^k-k\),
  \[
  0<b(T_{k,2^k-k})
  =O(\sqrt{k}/4^k)
  =O(\sqrt{\log n_k}/n_k^2),
  \qquad n_k=2^k+k+1,
  \]
  together with the exact expectation identity recorded in proof/INFORMAL_PROOF.md and HANDOVER.md.

There is no all-\(n\) or optimality claim. The extremal problem \(a_n=\min_{|V(T)|=n}b(T)\) remains optional/open and is not part of the frozen Stage-5 target.

## Proof and audit boundary

The proof of A is tree-structural. At a diameter endpoint, the support vertex has a pendant star and at most one nonleaf neighbour. Two or more pendant leaves force a greedy-vs-uniform marginal mismatch. Exactly one pendant leaf yields a canonical pair of maximal independent sets with strictly unequal greedy probabilities.

Stage 4 deliberately does **not** claim novelty for the process, iid-priority/RSA formulation, elementary first-choice/fibre recurrences, the maximal-independent-set count bound, or diameter-end tree geometry. New Stage-4 sources include Gadouleau–Kutner (2025), whose Example 1.1 already displays the unequal \(P_3\) permutation fibres, and Sagan–Vatter (2006), whose Proposition 1.7 supplies a standard maximal-set counting bound. Neither source subsumes A.

See audit/PRIOR_ART_NOVELTY_AUDIT.md and audit/SEARCH_LOG.md for the complete final audit.

## Reproducibility

The Stage-5 Lean environment is pinned to **Lean 4.34.1** and Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612` (Mathlib tag `v4.34.1`). The exact dependency graph is committed in `lake-manifest.json`. `GreedyUniformity/Bridge.lean` proves the exact finite-law bridge, and `GreedyUniformity/TheoremA.lean` proves Frozen A in both greedy-law and zero-bias graph-isomorphism forms. GitHub Actions run #84 passed the build, placeholder rejection, and all Python tests; `AxiomCheck.lean` reports only `propext`, `Classical.choice`, and `Quot.sound` for the final A theorems. See `formal/README.md` for the precise checkpoint boundary.

Lean build:

    lake build

Python regression suite:

    python -m pytest -q

The repository contains exact rational experiments with independent verification routes: exhaustive vertex permutations on tiny trees, first-vertex recursion, independent maximal-set enumeration, and a closed mixed-spider formula. The census covers all 436 nonisomorphic trees on 1–11 vertices and finds only \(K_1,K_2\) uniform.

Stage 3 added a targeted proof-certificate checker rather than a larger blind census. Across the 434 nontrivial trees through order 11 it checks 9 diameter-2 stars, 200 multi-leaf cases, 225 one-leaf cases, and 1103 exact paired-set inequalities. These computations test the proof; they are not the proof.

## Independence and integrity

This project is separate from **ProbStack — Random Stacking on Trees** and from TreeStack. No conclusion from those repositories is imported as evidence.

Lean formalisation has reached checkpoint 3, but Stage 5 is not complete: the finite-law bridge and Frozen Theorem A are formalised, while Frozen Theorem B remains. Palomar registration, paper writing, and arXiv submission have not begun. Stage 5 must continue without silently strengthening or weakening the frozen statements.

Start with PROJECT_CHARTER.md, CLAIMS.md, audit/PRIOR_ART_NOVELTY_AUDIT.md, audit/SEARCH_LOG.md, proof/INFORMAL_PROOF.md, experiments/VERIFIED_RESULTS.md, and HANDOVER.md.
