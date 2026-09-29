# Greedy Uniformity on Trees

Research repository for the distribution of random greedy maximal independent sets on finite trees.

## Current status

**Stages 1–3 completed on 2026-09-29. Stage 4 (final theorem-level prior-art/uniqueness audit) is next.**

Stage 2 gave **PASS FOR PROOF**, not a priority certificate. Stage 3 has now produced a complete informal structural proof of the exact tree obstruction, but the theorem is not frozen for Lean until Stage 4 checks the actual proved statement against the literature again.

The model: choose a uniformly random permutation of the vertices of a finite nonempty simple undirected tree, scan it once, and select a vertex iff no previously selected neighbour has been selected. The output is an inclusion-maximal independent set.

For a tree T, let \(G_T\) be the greedy output law and \(U_T\) uniform on its maximal independent sets \(\mathcal M(T)\). We study
\[
b(T)=\frac12\sum_{I\in\mathcal M(T)}
\left|G_T(I)-\frac1{|\mathcal M(T)|}\right|.
\]

## Stage-3 theorem package

- **A — proved informally, pending Stage-4 audit:** \(b(T)=0\) iff \(T\cong K_1\) or \(K_2\).
- **B — proved informally, pending Stage-4 audit:** the mixed spider \(T_{k,2^k-k}\) has positive bias tending to zero with \(O(\sqrt{k}/4^k)=O(\sqrt{\log n_k}/n_k^2)\) along \(n_k=2^k+k+1\).
- **C — optional/open:** determine sharp extremal behaviour of \(a_n=\min_{|V(T)|=n}b(T)\).

The proof of A is tree-structural. At a diameter endpoint, its support vertex has a pendant star and at most one nonleaf neighbour. Two or more pendant leaves force a mismatch between the greedy and uniform inclusion marginals. Exactly one pendant leaf yields a canonical pair of maximal independent sets with strictly unequal greedy probabilities, proved by an iid-priority certificate. See proof/INFORMAL_PROOF.md.

The proof document also derives the exact first-vertex recurrence, component factorisation, and integer permutation-fibre recurrence requested for later formalisation.

## Reproducibility

The repository contains exact rational experiments with independent verification routes: exhaustive vertex permutations on tiny trees, first-vertex recursion, independent maximal-set enumeration, and a closed mixed-spider formula. The original census covers all 436 nonisomorphic trees on 1–11 vertices and finds only \(K_1,K_2\) uniform.

Stage 3 added a **targeted** proof-certificate check rather than a larger blind census. On the 434 trees of orders 3–11 it verifies the local diameter-end cases used by the proof, including 1103 paired-set inequalities in the one-leaf case. These computations test the argument; they are not the proof.

## Independence and integrity

This project is separate from **ProbStack — Random Stacking on Trees** and from TreeStack. No conclusion from those repositories is imported as evidence.

The underlying greedy/RSA process and the general flat-vs-dynamical blocked-state comparison are prior art; the repository makes no novelty claim for them. No Lean formalisation, Palomar registration, research paper, or arXiv submission has been begun in this project yet.

Start with PROJECT_CHARTER.md, CLAIMS.md, audit/PRIOR_ART_NOVELTY_AUDIT.md, proof/INFORMAL_PROOF.md, experiments/VERIFIED_RESULTS.md, and HANDOVER.md.
