# Verified computational results — 2026-09-29

All probabilities and biases below were computed with exact integer/rational arithmetic.

## Independent methods from Stages 1–2

1. **Permutation enumeration.** For a tiny tree, enumerate every vertex permutation and run the deterministic greedy scan.
2. **First-vertex recursion.** Condition on the first vertex, remove its closed neighbourhood, and recurse on the induced residual forest.
3. **Maximal-set enumeration.** Independently enumerate subsets and test independence plus domination/maximality before computing total-variation bias.
4. **Closed mixed-spider formula.** Evaluate the proposed finite formula without using the recursion.

Methods 1 and 2 agree on every nonisomorphic tree through 7 vertices (25 tree classes). Methods 2 and 4 agree for all 12 pairs \(1\le k\le4\), \(1\le l\le3\), including the multiplicity \(\binom{k}{j}\) of non-centre output types.

## Unlabeled-tree census

The generated class counts for orders 1 through 11 are
\[
1,1,1,2,3,6,11,23,47,106,235,
\]
totalling 436. This agrees with OEIS A000055.

Exactly two of these 436 classes have zero bias: \(K_1\) and \(K_2\). Thus all 434 tree classes on 3–11 vertices tested have positive bias.

Minimum positive bias by order:

| n | min positive b(T) |
|---:|---:|
| 3 | 1/6 |
| 4 | 1/12 |
| 5 | 1/15 |
| 6 | 1/10 |
| 7 | 1/30 |
| 8 | 17/480 |
| 9 | 16/315 |
| 10 | 25/576 |
| 11 | 29/1260 |

These values are computational evidence only; they are not an extremal theorem for general \(n\).

## Mixed-spider family

For \(T_{k,l}\), with \(N=2^k\),
\[
p_c=\frac1N\sum_{j=0}^k\binom{k}{j}\frac1{l+2j+1},
\qquad
q_j=\frac{l+2j}{N(l+2j+1)}
\]
for each particular non-centre set containing \(j\) inner vertices, with multiplicity \(\binom{k}{j}\).

Selected exact values for \(l=2^k-k\):

| k | l | vertices | exact b(T) | decimal |
|---:|---:|---:|---:|---:|
| 2 | 2 | 7 | 1/30 | 0.0333333333 |
| 3 | 5 | 12 | 7/576 | 0.0121527778 |
| 4 | 12 | 21 | 41/13260 | 0.0030920060 |
| 6 | 58 | 71 | 18353/78602160 | 0.0002334923 |
| 10 | 1014 | 1035 | 22598757953479/19219192053894201600 | 0.0000011758433 |

## Stage-3 targeted proof-certificate checks

Stage 3 did **not** extend the blind census beyond order 11. Instead, experiments/stage3_targeted.py checks the local cases that arose in the structural proof.

On all 434 nonisomorphic trees of orders 3–11, a chosen diameter endpoint yields:

- 9 diameter-2 stars;
- 200 cases where the support has at least two leaf neighbours and one nonleaf neighbour;
- 225 cases where the support has exactly one leaf neighbour and one nonleaf neighbour.

For the 200 multi-leaf cases the script verifies the maximal-set count bound used for the uniform marginal and the strict greedy-vs-uniform marginal inequality.

For the 225 one-leaf cases it checks every residual maximal independent set \(A\), for 1103 paired-set comparisons total. In every pair the exact rational recursion agrees with the strict direction proved in Lemma 9 of proof/INFORMAL_PROOF.md.

Running

    python -m pytest -q tests/test_stage3_targeted.py

passes the targeted test: 1 passed.

## Limits of this evidence

- The computations are not used as a proof of the all-tree obstruction; Stage 3 has a separate complete informal proof.
- The mixed-spider finite checks do not replace the direct formula argument.
- No search beyond 11 vertices was run merely to accumulate examples.
- No all-\(n\) extremal conclusion or optimality claim is supported by these computations.
