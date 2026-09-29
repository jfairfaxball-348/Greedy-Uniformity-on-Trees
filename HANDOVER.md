# Proof-stage handover

**Date:** 2026-09-29  
**Completed:** Stage 1 (scaffold), Stage 2 (detailed prior-art/novelty audit)  
**Decision:** **PASS FOR PROOF**  
**Not completed:** Stages 3–8.

## Candidate theorem to pursue

For every finite nonempty tree (T), the random-permutation greedy maximal-independent-set law is uniform on the maximal independent sets iff (Tcong K_1) or (K_2).

Companion construction: with (T_k=T_{k,2^k-k}), (n_k=2^k+k+1),

[
0<b(T_k)
le
rac12left(
rac{k}{(2^k+1)^2(2^k+1-k)}
+
rac{sqrt{k}}{(2^k+1)(2^k+1-k)}
ight),
]

so (b(T_k)=O(sqrt{k}/4^k)=O(sqrt{log n_k}/n_k^2)).

The construction/formula is already a verified finite derivation. The exact obstruction is the serious unproved part. The statement is **not frozen** until Stage 4.

## First serious lemma

For any finite graph (G), maximal independent set (I), and (n=|V(G)|), derive and exploit the first-vertex recurrence

[
Pr_G(I)=rac1nsum_{vin I}Pr_{G-N[v]}(Isetminus{v}),
]

with the probability on a residual forest factored over connected components.

For trees, combine this recurrence with a leaf/support-vertex decomposition. The first proof objective is a **local imbalance lemma** strong enough to show that a uniformly distributed greedy terminal law forces a restrictive leaf structure.

A particularly useful milestone would be either:

1. **Uniform greedy law on a tree => well-covered tree**, after which Ravindra reduces the candidates to (K_1) and coronas; or
2. the stronger **uniform greedy law on a tree => regular independent sets** in the sense of Kryven–Versendaal–de Vries, which would immediately force a connected nontrivial tree to be (K_2).

Neither implication is currently proved and neither should be assumed.

## Plausible proof approaches

### Route A — leaf/support probability comparison
Root at a leaf (x) with support (y). Construct paired maximal independent sets that locally choose (x) versus (y) while controlling the residual components. Use the first-vertex recurrence to show equality of all terminal probabilities imposes an equation on the attached subtrees. Iterate the equation toward the core.

Desired outcome: every internal vertex is forced to have exactly one leaf neighbour (well-covered/corona structure), then a second local comparison rules out every nontrivial corona.

### Route B — permutation fibre counts
Let (g_T(I)) be the number of permutations yielding (I). Uniformity is equivalent to constant (g_T(I)) over all maximal independent sets. Derive an integer recursion for (g_T(I)), including multinomial interleavings after deletion of (N[v]). Divisibility or parity constraints may expose an unavoidable discrepancy between carefully chosen maximal sets.

This route is attractive for Lean later because it avoids analytic probability.

### Route C — necessity of regular independent sets on trees
Try to prove a tree-specific converse to Proposition 3.8: exact terminal uniformity forces equal residual available counts for equal-sized independent sets. A full general-graph converse is probably too ambitious; exploit acyclicity and leaf pruning.

### Route D — generating functions / rooted states
Define rooted-tree recurrences for:
- the number of maximal independent sets of each boundary type;
- the total permutation fibre mass of each boundary type.

Uniformity would equate two recursively defined ratios. Seek a monotonicity or strict-convexity statement showing the ratios cannot all coincide except for (K_1,K_2).

## Targeted counterexample search before committing to a proof architecture

Do **not** run a larger blind census merely for reassurance. Search only classes implicated by the proof routes:

- well-covered trees / coronas beyond the existing range;
- highly symmetric spiders and double-stars;
- trees whose leaf-support structure could defeat a local imbalance lemma;
- minimal examples where different maximal-set sizes coexist.

If a counterexample (T) with (|T|ge3) and (b(T)=0) is found, A is false and takes precedence over the desired narrative.

## What would make us abandon or revise the target

1. **Mathematical counterexample:** any verified nontrivial uniform tree kills A.
2. **Prior-art implication:** a checked published/preprint theorem gives an exact converse/characterization that makes A routine.
3. **Construction priority collision:** a prior source already contains the mixed-spider formula/tuning/rate; then B loses its novelty role.
4. **Proof trivialization:** if A follows in a few routine lines from a standard characterization, A+B may be too light; reconsider C, a stability theorem, or an all-n sharp result.
5. **Proof-route failure without replacement:** if work only proves the obstruction for well-covered/corona trees but cannot justify why uniformity implies that class, do not promote the partial result to A.
6. **No arbitrary rescue:** do not add artificial restrictions or rename the same quantity merely to avoid a failed novelty audit.

## Stage-3 deliverables

Stage 3 must contain:
- a complete informal proof or a counterexample;
- a dependency map showing exactly which lemmas are proved;
- clear separation of theorem, lemmas, conjectures and computation;
- the B construction proof written cleanly as part of the theorem package if A survives;
- no Lean claim beyond exploratory notes.

After Stage 3, Stage 4 must re-audit the **actual proved statement** before anything is frozen or formalised.
