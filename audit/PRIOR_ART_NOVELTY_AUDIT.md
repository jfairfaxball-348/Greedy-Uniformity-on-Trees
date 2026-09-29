# Detailed prior-art and novelty audit

**Audit date:** 2026-09-29  
**Stage:** 2 of 8  
**Verdict:** **PASS FOR PROOF**, with bounded novelty uncertainty described below.

This is a priority audit, not a certificate that no equivalent theorem exists anywhere. The project may proceed to proof research, but the theorem must be re-audited after the actual proof is known.

## 1. Target under audit

For a finite nonempty simple undirected tree (T), place the vertices in uniformly random order and greedily accept a vertex exactly when no previously accepted neighbour is present. Let (G_T) be the law of the resulting maximal independent set, (U_T) uniform on the set (mathcal M(T)) of maximal independent sets, and

[
b(T)=d_{m TV}(G_T,U_T).
]

The proposed programme is:

- **A. Exact obstruction:** (b(T)=0) iff (T=K_1) or (K_2).
- **B. Arbitrarily close approximation:** an explicit connected family has (b(T)>0) but (b(T)	o0), quantitatively.
- **C. Extremal extension:** understand (a_n=min{b(T): |T|=n}).

A remains unproved. B has a direct finite calculation and exact computational checks. C is not an established consequence of A+B.

## 2. Reproduction before novelty assessment

The preliminary evidence was independently reconstructed rather than copied.

- Generated nonisomorphic trees on 1–11 vertices. The class counts
  (1,1,1,2,3,6,11,23,47,106,235) total 436 and agree with OEIS A000055.
- Computed the greedy output law with exact first-vertex recursion.
- Independently enumerated every vertex permutation for all 25 nonisomorphic trees through 7 vertices; those distributions agree exactly with the recursion.
- Independently enumerated maximal independent sets as subsets before computing total-variation distance.
- Exactly (K_1,K_2) are uniform in the 1–11 census; all 434 classes on 3–11 vertices are biased.
- Checked the mixed-spider formula against recursion for the 12 cases (1le kle4), (1le lle3), with the probability of a *particular* non-centre set kept separate from its multiplicity (inom{k}{j}).

See `experiments/VERIFIED_RESULTS.md` and the executable code/tests.

The supplied `Independent_Combinatorics_Directions_2026-09-28.md` was found in the Library and treated as a discovery record only. The named experiment ZIP was not available in the accessible Library and therefore was not used.

## 3. Exact model equivalences and distinctions

The process itself is classical.

Krivelevich–Mészáros–Michaeli–Shikhelman, *Greedy maximal independent sets via local limits* (arXiv:1907.07216; later Random Structures & Algorithms), define the same uniformly random vertex-order greedy MIS. They also give the equivalent iid continuous arrival-time formulation. Their central quantities are the size/density of the output and its asymptotics under local convergence, including random-tree settings.

Dall'Asta–Pin–Ramezanpour, *Statistical Mechanics of maximal independent sets* (arXiv:0907.3309v2), Section V.1, describe Gazmuri's algorithm: repeatedly choose a uniformly random remaining vertex, occupy it, and remove it with its neighbours. On a fixed finite graph this has the same law as restricting a uniformly random permutation to the currently available vertices. Their analysis is chiefly density/large deviations on random graph ensembles.

This makes the following distinctions mandatory:

- fixed deterministic tree vs a random tree or a graph sequence;
- maximal independent sets vs maximum independent sets;
- a uniform random permutation / equivalent random-priority process vs other local dynamics;
- the probability of each complete terminal set vs output size, density, vertex marginals, or occupancy probabilities.

The terminology of blocking random sequential adsorption (RSA), parking, jammed states and blocked configurations is relevant. Dehling–Fleurke–Külske, *Parking on a Random Tree* (J. Stat. Phys. 133 (2008), arXiv:0711.4061), and Sudbury, *Random sequential adsorption on random trees* (J. Stat. Phys. 136 (2009)), study blocking RSA on tree structures, principally occupation probabilities and parking constants. These sources establish that neither the process nor tree RSA is new.

Dall'Asta–Pin–Ramezanpour also explicitly discuss the difference between a static Edwards-type treatment of blocked configurations and a dynamical measure whose basin sizes need not be equal. Therefore the broad idea “compare a dynamic greedy measure with a flat measure on jammed states” is prior art. The possible novelty here must lie in the exact finite-tree classification and quantitative near-uniformity, not in that conceptual contrast.

## 4. Closest exact-uniformity result: Kryven–Versendaal–de Vries (2026)

The closest source located is Ivan Kryven, Rik Versendaal and Mike de Vries, *Unified framework for asymptotically uniform iterative construction of generalised random graphs with local constraints*, arXiv:2608.07239v1 (submitted 2026-08-07).

The following locations were checked in the full text:

- **Definition 3.6:** the Iterative Maximal Independent Set (IMIS) process chooses uniformly from the vertices still available after the current independent set. For a finite graph, this is equivalent in law to the random-permutation process here.
- **Definition 3.7:** “regular independent sets” require the number of available vertices after an independent set to depend only on its cardinality (equivalently, equal-sized independent sets have equally sized closed neighbourhoods).
- **Proposition 3.8:** under regular independent sets, all possible IMIS sequences of a given length have equal probability; maximal independent sets are maximum, and the terminal IMIS is uniform on maximal independent sets.
- **Definition 3.13:** 2-uniformity adds a condition on the number of neighbours outside a maximal independent set.
- The discussion following Definition 3.13 notes that regular independent sets already force ordinary vertex regularity by applying the condition to one-vertex independent sets.
- **Theorem 3.23:** classifies 2-uniform graphs; it is used for the paper's asymptotically uniform construction framework.

For a connected finite tree, vertex regularity leaves only (K_2) among non-edgeless trees; (K_1) is the separate edgeless case. Thus the displayed sufficient condition of Proposition 3.8 excludes every nontrivial tree relevant to A.

**Crucially, Proposition 3.8 is not a converse.** The checked statements do not say that an exactly uniform IMIS law forces regular independent sets or 2-uniformity. The classification of 2-uniform graphs therefore does not settle A. The strongest specific novelty risk remaining is that a converse, reduction, or equivalent characterization appears elsewhere in this paper's references or in older terminology.

The source's title and abstract use “2-uniformity” in connection with preservation of *asymptotic* uniformity in its configuration-model applications. That should not be conflated with the present exact finite-tree terminal-law question.

## 5. Random trees and output-size laws

Alice Contat, *Surprising identities for the greedy independent set on Cayley trees* (arXiv:2103.03800), proves an exact distributional identity for the **size** (G_n) of the greedy independent set on a **uniform Cayley tree**. It does not give the probabilities of individual maximal independent sets of a fixed deterministic tree.

Krivelevich et al. explicitly place Contat's result in the uniform-random-tree / cardinality setting and discuss expected densities on trees. This is adjacent but does not imply A or B.

Panholzer's work on parking/greedy occupation on random labelled trees likewise concerns aggregate occupation counts, moments, limiting densities, or random-tree laws rather than exact equiprobability of complete terminal sets for a fixed tree.

## 6. Static uniform measures on independent sets

The hard-core model at fugacity (1) is uniform on **all independent sets**, not on maximal independent sets. Results on sampling from that measure do not answer the present question.

There is a substantial literature on well-covered graphs, where every maximal independent set has the same cardinality. Equal cardinality is much weaker than equal greedy probability. Ravindra's classical characterization implies that a tree is well-covered iff it is (K_1) or a corona of a tree (equivalently, for a nontrivial tree, the pendant edges form a perfect matching). This may become a useful proof tool if Stage 3 can prove a new implication such as

[
	ext{uniform greedy terminal law on a tree}Longrightarrow	ext{well-covered}.
]

No such implication was assumed or located during this audit.

## 7. Mixed spiders / subdivided stars

Targeted searches used the terms spider, spider tree, subdivided star, starlike tree, mixed length-one/length-two arms, blocking RSA, random greedy independent set, maximal independent set and uniform/equiprobable output.

No primary source was located that states the formula for the mixed family (T_{k,l}), its tuning (l=2^k-k), or the rate below. This is negative search evidence only.

The graph family itself is standard: it is a spider with arms of lengths one and two. Novelty cannot rest on naming or drawing the family.

## 8. Direct audit of the construction B

Let (N=2^k). The maximal independent sets of (T_{k,l}) are:

1. the unique centre-containing set ({c,v_1,ldots,v_k});
2. (N) non-centre sets containing every direct leaf and exactly one endpoint of each two-edge arm.

Give vertices iid continuous priorities. If the centre is temporarily ignored, every arm chooses one endpoint with probability (1/2), independently. Fix one resulting non-centre pattern containing exactly (j) inner vertices (u_i). Reinserting (c) changes this pattern exactly when (c) precedes all (l) direct leaves and both endpoints of each of those (j) arms. Conditional on the required pair-orders on the arms, that event has probability (1/(l+2j+1)). Hence

[
q_j=rac{l+2j}{N(l+2j+1)}
]

for each particular non-centre pattern of type (j), with multiplicity (inom{k}{j}), and

[
p_c=rac1Nsum_{j=0}^kinom{k}{j}rac1{l+2j+1}.
]

This direct argument is independent of the first-vertex recursion used in the computation.

Now put (l=N-k), (A=N+1), (Jsim{m Bin}(k,1/2)), (W=2J-k). Direct substitution gives

[
b(T_{k,N-k})=
rac12left(
mathbb Erac{W^2}{A^2(A+W)}
+
mathbb Erac{|W|}{A(A+W)}
ight).
]

Since (W) is nonzero with positive probability for every (kge1), the bias is positive. Also (A+Wge A-k), (mathbb E W^2=k), and (mathbb E|W|lesqrt{k}), so

[
b(T_{k,N-k})
le
rac12left(
rac{k}{A^2(A-k)}
+
rac{sqrt{k}}{A(A-k)}
ight)
=O!left(rac{sqrt{k}}{4^k}ight).
]

As (n_k=N+k+1), this is
(O(sqrt{log n_k}/n_k^2)) along the stated subsequence.

This establishes the correctness of the proposed construction/rate as a finite mathematical derivation. It does **not** establish optimality, an all-(n) bound, or priority.

## 9. Audit matrix

| Target | Audit classification | Reason |
|---|---|---|
| **A: exact obstruction on trees** | **Plausibly new and substantive target** | Same stochastic process is classical, but no checked source gives the fixed-tree converse/classification. The closest 2026 exact-uniformity result is sufficient, not necessary. Exhaustive evidence through 11 vertices supports but does not prove A. |
| **B: explicit mixed-spider formula and vanishing bias rate** | **Plausibly new; construction itself is elementary once found** | Formula independently derived and checked; targeted searches did not locate it. No optimality is claimed. B alone would be a modest contribution; paired with A it supplies the “exactly impossible / arbitrarily close” phenomenon. |
| **C: (a_n) extremal problem** | **Unresolved open research direction** | No direct prior theorem was located, but this audit was not designed to clear a sharp all-(n) extremal law. Current experiments are too small to support a structural conjecture beyond evidence. |

None of A–C is classified as “already known” or as a routine consequence of a checked result. That classification is conditional on the source coverage recorded here; it is not worldwide priority clearance.

## 10. Strongest objection to originality and significance

The strongest objection is cumulative:

1. the greedy/random-priority/RSA process is old;
2. maximal independent sets as blocked or jammed states are old;
3. the distinction between a flat blocked-state ensemble and a dynamical measure is old;
4. Gazmuri's algorithm is the same finite greedy law in another implementation;
5. the August 2026 Kryven–Versendaal–de Vries preprint explicitly connects IMIS with uniform maximal-independent-set sampling under a structural condition;
6. once the mixed-spider family is guessed, its probability formula is short.

Accordingly, the project should make **no** novelty claim for the algorithm, the TV metric, the static-vs-dynamic comparison, or the existence of spiders. The research contribution must be the exact necessity theorem for trees together with the sharp contrast furnished by an explicit near-uniform family.

## 11. Is C required?

**Not at the proof-investment stage.** If A requires a genuinely structural argument, then A+B form a coherent theorem of independent interest: within connected trees, exact flatness of the terminal measure is confined to trivial cases, yet the dynamic law can approach the flat measure quadratically fast in the number of vertices along an explicit subsequence.

C would materially strengthen the paper, but it is not needed merely to justify trying to prove A. Conversely, if Stage 3 reveals that A is an immediate consequence of an existing characterization or a very short routine lemma, then A+B may be too light; at that point C, a stability theorem, an all-(n) construction, or another genuine structural advance would need to be reconsidered. Arbitrary restrictions or renaming the quantity would not rescue the target.

## 12. Search/access limitations

Checked material includes primary arXiv/full-text sources, publisher/author pages, and citation trails. Searches covered the requested synonyms plus newer exact-uniformity terminology. The audit did not include an exhaustive subscription-only MathSciNet or zbMATH review or author correspondence. A missing web keyword match is not treated as clearance.

The supplied discovery markdown was available. The supplied experiment ZIP was not located in the accessible Library, but all stated tree computations needed for this audit were independently reconstructed.

## 13. Decision

# PASS FOR PROOF

Proceed to Stage 3 with the following central candidate:

> **Candidate theorem.** For every finite nonempty tree (T), the random-permutation greedy maximal-independent-set law is uniform on (mathcal M(T)) iff (Tcong K_1) or (K_2). Nevertheless, for (T_k=T_{k,2^k-k}), (b(T_k)>0) and (b(T_k)=O(sqrt{k}/4^k)=O(sqrt{log n_k}/n_k^2)) along (n_k=2^k+k+1).

The B part is already a verified lemma-level calculation; **A is the serious proof problem**. Passing this audit authorizes proof research only. It does not freeze the theorem and does not establish uniqueness.
