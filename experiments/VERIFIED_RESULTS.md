# Verified computational results — 2026-09-29

All probabilities and biases below were computed with exact integer/rational arithmetic.

## Independent methods

1. **Permutation enumeration.** For a tiny tree, enumerate every vertex permutation and run the deterministic greedy scan.
2. **First-vertex recursion.** Condition on the first vertex, remove its closed neighbourhood, and recurse on the induced residual forest.
3. **Maximal-set enumeration.** Independently enumerate subsets and test independence plus domination/maximality before computing total-variation bias.
4. **Closed mixed-spider formula.** Evaluate the proposed finite formula without using the recursion.

Methods 1 and 2 agree on every nonisomorphic tree through 7 vertices (25 tree classes). Methods 2 and 4 agree for all 12 pairs (1\le k\le4), (1\le l\le3), including the multiplicity (inom{k}{j}) of non-centre output types.

## Unlabeled-tree census

The generated class counts for orders 1 through 11 are

[
1,1,1,2,3,6,11,23,47,106,235,
]

totalling 436. This agrees with OEIS A000055, the standard count of unlabeled trees.

Exactly two of these 436 classes have zero bias: (K_1) and (K_2). Thus all 434 tree classes on 3–11 vertices tested have positive bias.

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

These values are computational evidence only; they are not an extremal theorem for general n.

## Mixed-spider family

For (T_{k,l}), with (N=2^k),

[
p_c=\frac1N\sum_{j=0}^k \binom{k}{j}\frac1{l+2j+1},
qquad
q_j=\frac{l+2j}{N(l+2j+1)}
]

for each particular non-centre set containing (j) inner vertices. The multiplicity of that probability is (inom{k}{j}).

Selected exact values for (l=2^k-k):

| k | l | vertices | exact b(T) | decimal |
|---:|---:|---:|---:|---:|
| 2 | 2 | 7 | 1/30 | 0.0333333333 |
| 3 | 5 | 12 | 7/576 | 0.0121527778 |
| 4 | 12 | 21 | 41/13260 | 0.0030920060 |
| 6 | 58 | 71 | 18353/78602160 | 0.0002334923 |
| 10 | 1014 | 1035 | 22598757953479/19219192053894201600 | 0.0000011758433 |

No discrepancy was found with the supplied discovery record.

## Limits of this evidence

- The 1–11 census does not prove the obstruction conjecture.
- The mixed-spider finite checks do not replace the direct formula argument.
- No search beyond 11 vertices was run merely to accumulate examples.
- The missing discovery ZIP was not used; the code in this repository was reconstructed independently from the mathematical specification.
