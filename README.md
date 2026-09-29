# Greedy Uniformity on Trees

Research repository for the distribution of random greedy maximal independent sets on finite trees.

## Status

Stages 1–2 are in progress. Originality, significance, and the proposed theorems are **questions under audit**, not project assumptions. No theorem in this repository should be cited as proved unless the claim ledger marks it proved and points to a complete proof.

The model: choose a uniformly random permutation of the vertices of a finite nonempty simple undirected tree, scan once, and select a vertex iff no previously selected neighbour has been selected. The output is an inclusion-maximal independent set.

For a tree (T), let (G_T) be the greedy output law and (U_T) uniform on the maximal independent sets. We study
[
b(T)=\tfrac12\sum_{I\in\mathcal M(T)} |G_T(I)-1/|\mathcal M(T)||.
]

This project is independent of **ProbStack — Random Stacking on Trees** and does not use ProbStack or TreeStack conclusions as evidence.

See `PROJECT_CHARTER.md`, `ROADMAP.md`, `CLAIMS.md`, `audit/`, `experiments/`, and `HANDOVER.md`.
