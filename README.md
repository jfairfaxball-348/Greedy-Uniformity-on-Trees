# Greedy Uniformity on Trees

Research repository for the distribution of random greedy maximal independent sets on finite trees.

## Current status

**Stages 1 and 2 completed on 2026-09-29. Audit decision: PASS FOR PROOF.**

That decision means the exact obstruction plus the explicit near-uniform family are a mathematically substantive, plausibly new target worth investing proof effort in. It is **not** a claim of worldwide priority, and the obstruction is still a conjecture.

The model: choose a uniformly random permutation of the vertices of a finite nonempty simple undirected tree, scan it once, and select a vertex iff no previously selected neighbour has been selected. The output is an inclusion-maximal independent set.

For a tree (T), let (G_T) be the greedy output law and (U_T) uniform on its maximal independent sets (mathcal M(T)). We study

[
b(T)=rac12sum_{Iinmathcal M(T)}
left|G_T(I)-rac1{|mathcal M(T)|}ight|.
]

## Candidate programme

- **A — unproved:** (b(T)=0) iff (Tcong K_1) or (K_2).
- **B — verified construction:** the mixed spider (T_{k,2^k-k}) has positive bias tending to zero with (O(sqrt{k}/4^k)=O(sqrt{log n_k}/n_k^2)) along (n_k=2^k+k+1).
- **C — optional/open:** determine sharp extremal behaviour of (a_n=min_{|V(T)|=n} b(T)).

The detailed audit concludes that A+B are worth pursuing without making C mandatory at this stage, provided A requires a genuinely structural proof. See `audit/PRIOR_ART_NOVELTY_AUDIT.md`.

## Reproducibility

The repository contains exact rational experiments with independent verification routes: exhaustive vertex permutations on tiny trees, first-vertex recursion, independent maximal-set enumeration, and a closed mixed-spider formula. The census covers all 436 nonisomorphic trees on 1–11 vertices and finds only (K_1,K_2) uniform. This is computational evidence, not a proof of A.

## Independence and integrity

This project is separate from **ProbStack — Random Stacking on Trees** and from TreeStack. No conclusion from those repositories is imported as evidence.

The underlying greedy/RSA process and the general flat-vs-dynamical blocked-state comparison are prior art; the repository makes no novelty claim for them. No Lean formalisation, Palomar registration, research paper, or arXiv submission has been begun in this project yet.

Start with `PROJECT_CHARTER.md`, `CLAIMS.md`, `audit/PRIOR_ART_NOVELTY_AUDIT.md`, `experiments/VERIFIED_RESULTS.md`, and `HANDOVER.md`.
