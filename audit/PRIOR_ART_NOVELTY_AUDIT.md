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

---

# Stage-4 final theorem-level prior-art / uniqueness audit

**Audit date:** 2026-09-29  
**Stage:** 4 of 8  
**Objects audited:** the exact Stage-3 Theorems A and B, together with the proof shape actually used.  
**Verdict:** **PASS — FREEZE FOR FORMALISATION.**

This section is the post-proof audit required by the project workflow. It does not rewrite the historical Stage-2 verdict above. Stage 2 authorized proof research; this Stage-4 audit asks whether the theorem that was actually proved is already known, is a routine corollary, or is materially subsumed by checked literature.

The verdict is deliberately bounded: **plausibly new with bounded uncertainty**, not a claim of worldwide uniqueness or priority.

## 14. Frozen Stage-3 statements under audit

### A — exact obstruction

For every finite nonempty simple undirected tree \(T\),
\[
G_T=U_T
\quad\Longleftrightarrow\quad
T\cong K_1\text{ or }K_2.
\]
Equivalently, \(b(T)=0\) iff \(T\cong K_1\) or \(K_2\).

### B — mixed-spider near-uniformity

For the mixed spider \(T_{k,l}\) with centre \(c\), \(k\) arms \(c-u_i-v_i\) and \(l\) additional leaves at \(c\), put \(N=2^k\). There are \(N+1\) maximal independent sets. The unique centre-containing set has probability
\[
p_c=\frac1N\sum_{j=0}^k\binom{k}{j}\frac1{l+2j+1},
\]
and each particular non-centre maximal independent set containing exactly \(j\) inner vertices \(u_i\) has probability
\[
q_j=\frac{l+2j}{N(l+2j+1)},
\]
with multiplicity \(\binom{k}{j}\).

For \(l=2^k-k\), let \(A=2^k+1\), \(J\sim{\rm Bin}(k,1/2)\), \(W=2J-k\), and \(n_k=2^k+k+1\). Then
\[
b(T_{k,2^k-k})
=\frac12\left(
\mathbb E\frac{W^2}{A^2(A+W)}
+\mathbb E\frac{|W|}{A(A+W)}
\right)>0,
\]
and
\[
b(T_{k,2^k-k})
=O\!\left(\frac{\sqrt{k}}{4^k}\right)
=O\!\left(\frac{\sqrt{\log n_k}}{n_k^2}\right)
\qquad(k\to\infty).
\]
No all-\(n\), sharp extremal, lower-bound, or optimality assertion is included.

## 15. Recheck of the closest 2026 source

The current arXiv record for Ivan Kryven, Rik Versendaal and Mike de Vries, *Unified framework for asymptotically uniform iterative construction of generalised random graphs with local constraints*, is still arXiv:2608.07239v1, submitted 2026-08-07. No later arXiv revision was present when this audit was run.

The decisive locations were re-read in the current v1 HTML:

- **Definition 3.6:** the IMIS process repeatedly chooses uniformly from vertices outside the closed neighbourhood of the current independent set. On a finite graph this is the same law as random-permutation greedy MIS.
- **Definition 3.7:** “regular independent sets” means the number of available vertices after an independent set depends only on its size.
- **Proposition 3.8:** regular independent sets imply that every IMIS sequence is equally likely, all maximal independent sets are maximum, and the terminal IMIS is uniform.
- **Definition 3.13:** 2-uniformity adds a further two-neighbours-in-each-MIS condition to regular independent sets.
- **Theorem 3.23:** classifies 2-uniform graphs as configuration spaces, bipartite configuration spaces, \(K_{k\times2}\), or the Schläfli graph.

The key logical point remains unchanged from Stage 2: **Proposition 3.8 is sufficient, not converse.** No statement in the checked current version proves
\[
\text{uniform IMIS output}\Longrightarrow\text{regular independent sets}
\]
or
\[
\text{uniform IMIS output}\Longrightarrow\text{2-uniformity}.
\]
Therefore Theorem 3.23 does not classify all graphs having uniform IMIS output and does not make Theorem A a routine specialization.

There is a useful one-way consistency check: equality of the regular-independent-set parameter on singleton independent sets forces ordinary vertex-regularity. Hence a connected tree satisfying the sufficient hypothesis of Proposition 3.8 is \(K_1\) or \(K_2\). This recovers the positive examples under a stronger hypothesis; it does **not** prove the necessity direction of A.

The classification citation in Theorem 3.23 was chased to François Zara, *Graphes Lies aux Espaces Polaires*, European Journal of Combinatorics 5 (1984), 255–290, especially the source identified by Kryven–Versendaal–de Vries as Section 7, Part A, Remark 7.7. Zara studies graphs satisfying fixed maximal-clique size (A1) and a fixed number \(t\) of neighbours into each maximal clique (A2), including the \(t=r-2\) classification used after complementation. This is a structural antecedent of the 2-uniform classification, not a theorem about random greedy terminal probabilities.

## 16. Audit of A against adjacent literature

### Same process, different observable

Krivelevich–Mészáros–Michaeli–Shikhelman, *Greedy maximal independent sets via local limits*, uses exactly the random-order greedy MIS process and the equivalent iid-\([0,1]\)-label representation. Its primary observable is the **size/density** of the resulting set and asymptotics under local convergence, including trees. It does not supply a finite-tree characterization of when the complete terminal set is equiprobable over all maximal independent sets.

Nicholas Pippenger, *Random Sequential Adsorption on Graphs* (SIAM J. Discrete Math. 2 (1989), 393–401), is an early exact match to the random-order blocking/RSA dynamics. It studies occupation probabilities and jamming limits on regular/high-girth graphs and related lattices. It does not classify finite trees by the full terminal configuration law.

Dall'Asta–Pin–Ramezanpour, *Statistical Mechanics of maximal independent sets*, explicitly places maximal independent sets in the blocked-state/Edwards-measure setting and Section V.1 gives Gazmuri's sequential greedy algorithm. The paper studies densities and large deviations in random graph ensembles, not equality of all complete-output probabilities on a fixed finite tree.

Thus the algorithm, iid-priority/RSA language, and flat-versus-dynamical comparison are background, not contributions of this project.

### A new 2025 overlap: deterministic reachability and the smallest biased tree

Maximilien Gadouleau and David C. Kutner, *Generalising the maximum independent set algorithm via Boolean networks*, Information and Computation 303 (2025), 105266, studies the same deterministic greedy MIS map under arbitrary update words and starting configurations. **Example 1.1** is the path \(P_3\): from the empty set the two permutations beginning at the middle vertex yield the singleton middle MIS, while the other four permutations yield the two-endpoint MIS.

This explicitly exhibits unequal permutation-fibre sizes for the smallest nontrivial tree and should be acknowledged. The paper's theorems concern reachability, fixing words, fixing permutations (“permises”), and complexity; no checked theorem characterizes graphs or trees for which a uniformly random permutation yields a uniform distribution over maximal independent sets. It therefore overlaps an example and the deterministic map, but does not subsume A.

### Terminology false positive: “equal weight”

Caro–Ellingham–Ramey, *Local Structure When All Maximal Independent Sets Have Equal Weight*, SIAM J. Discrete Math. 11 (1998), 644–654, is not about output probability or basin size. “Weight” is the sum of assigned vertex weights in an abelian group, encompassing well-coveredness and parity questions. It is relevant to avoid a misleading title match, but it does not collide with A.

### No checked graph characterization implying A

Searches using “equiprobable maximal independent sets”, “equal basin sizes”, “greedy permutation fibres”, “uniform maximal independent set output”, “random-order greedy MIS”, IMIS, RSA, parking, jammed/blocked states, Edwards/dynamical measures, trees/forests/acyclic graphs, and graph-characterization terminology did not locate:

1. a necessary-and-sufficient characterization of graphs with exact uniform greedy MIS output;
2. a converse to Kryven–Versendaal–de Vries Proposition 3.8;
3. a stronger graph theorem whose specialization to connected trees immediately yields \(K_1,K_2\);
4. a finite-tree theorem equivalent to A.

This is a bounded negative search, not proof of absence.

### Classification for A

**A: plausibly new with bounded uncertainty.** It is not already known, a routine corollary, or materially subsumed by any checked result.

## 17. Proof-shape overlap

The audit distinguishes standard ingredients from the contribution-level assembly.

### Background / elementary ingredients

- Greedy scanning produces a maximal independent set.
- Uniform random order, iid continuous priorities, and repeated uniform choice among currently available vertices are equivalent formulations.
- Component factorisation and conditioning on the first selected vertex are elementary consequences of the process.
- The integer permutation-fibre recurrence is the counting form of that conditioning/interleaving argument. No exact prior statement was located, but it is elementary and is **not** claimed as a novelty contribution.
- The iid-priority certificate and its integral are a direct fixed-output consequence of the standard iid-priority formulation. The exact displayed integral was not located in the checked sources, but the project does **not** rely on novelty of this lemma.
- The diameter-end pendant-star structure is elementary tree geometry.
- The maximal-independent-set counting machinery is standard. In particular, Sagan–Vatter, *Maximal and maximum independent sets in graphs with at most r cycles*, Proposition 1.7 gives the standard “m-bound”
  \[
  m(G)\le m(G-v)+m(G-N[v]).
  \]
  Stage-3 Lemma 6, \(m(H)\le2m(H-v)\), is a short consequence after comparing \(m(H-N[v])\) with \(m(H-v)\). It is not a novelty claim.

### Assembly not found in the checked literature

No checked source used the Stage-3 diameter-end split to prove complete-output nonuniformity:

- two or more leaves at the support vertex via a greedy-vs-uniform inclusion marginal;
- exactly one pendant leaf via the canonical pair \(I_y\) versus \(I_x\) and a strict priority comparison for every residual maximal set.

Individual ingredients are standard or elementary. The audited contribution is the structural assembly yielding the exact all-tree obstruction, not ownership of those ingredients.

The unproved implication “uniform greedy law \(\Rightarrow\) well-covered” remains unclaimed and unused.

## 18. Audit of B

Searches covered spider tree, starlike tree, subdivided star, mixed arms of lengths one and two, RSA/parking on spiders, greedy MIS on spiders, terminal-state probabilities, almost/near/asymptotically uniform greedy laws, and direct formula fragments.

No checked source contained the pair
\[
p_c=\frac1{2^k}\sum_{j=0}^k\binom{k}{j}\frac1{l+2j+1},
\qquad
q_j=\frac{l+2j}{2^k(l+2j+1)},
\]
the tuning \(l=2^k-k\), or an equivalent construction giving the Stage-3 expectation identity and
\[
O(\sqrt{k}/4^k)=O(\sqrt{\log n_k}/n_k^2)
\]
along connected trees.

Searches for a stronger existing theorem asserting arbitrary closeness of the random greedy complete-output law to the uniform maximal-independent-set law on connected trees also returned no relevant result. Hits about greedy independent sets being near-optimal refer to **cardinality/optimization**, not total-variation proximity of complete-output laws.

### Classification for B

**B: plausibly new with bounded uncertainty.** No checked source gives the exact family/formula/tuning/rate or a stronger connected-tree construction that would subsume it.

## 19. Discrepancies and refinements relative to Stage 2

There is no priority collision and no theorem revision forced by Stage 4.

Stage 4 nevertheless sharpens the novelty boundary in four ways:

1. the Kryven–Versendaal–de Vries arXiv record was rechecked and remains v1; its exact-uniformity result is still one-way;
2. Gadouleau–Kutner (2025) is now recorded as a close deterministic-algorithm source and as an explicit \(P_3\) permutation-fibre example;
3. Sagan–Vatter Proposition 1.7 makes clear that the maximal-set counting inequality used in the proof is standard/background-level;
4. Caro–Ellingham–Ramey's “equal weight” terminology is explicitly separated from equal output probability.

These refinements reduce the set of ingredients that should ever be described as novel; they do not alter A or B.

## 20. Audit limitations

This audit used primary arXiv/manuscript/publisher sources where decisive, plus citation chasing from the closest paper. It did not amount to an exhaustive search of every subscription-only MathSciNet/zbMATH record, unpublished manuscript, thesis, or non-English source, and no author correspondence was undertaken. The August 2026 Kryven–Versendaal–de Vries preprint is recent, so its citation network can still change.

For that reason the correct language is **plausibly new with bounded uncertainty**, not “definitely novel” or “unique worldwide”.

## 21. Stage-4 verdict

# PASS — FREEZE FOR FORMALISATION

The checked literature leaves the proved A+B package plausibly new and mathematically substantive enough to proceed. A is a nontrivial structural necessity theorem for every finite tree; B supplies a quantitatively near-uniform connected-tree sequence showing that the exact obstruction has no fixed positive total-variation gap.

### Exact frozen package for Stage 5

**Frozen A.** For every finite nonempty simple undirected tree \(T\), the random-permutation greedy maximal-independent-set law is uniform on \(\mathcal M(T)\) iff \(T\cong K_1\) or \(K_2\). Equivalently \(b(T)=0\) iff \(T\cong K_1\) or \(K_2\).

**Frozen B.** For \(T_{k,l}\), the \(2^k+1\) maximal independent sets have exact probabilities \(p_c\) and \(q_j\) displayed in Section 14. For \(l=2^k-k\),
\[
0<b(T_{k,2^k-k})
=\frac12\left(
\mathbb E\frac{W^2}{A^2(A+W)}
+\mathbb E\frac{|W|}{A(A+W)}
\right)
=O(\sqrt{k}/4^k)
=O(\sqrt{\log n_k}/n_k^2),
\]
where \(A=2^k+1\), \(J\sim{\rm Bin}(k,1/2)\), \(W=2J-k\), and \(n_k=2^k+k+1\).

There is **no** all-\(n\) or optimality claim. C remains optional/open and is not part of the frozen formalisation target.

Stage 5 may now formalise exactly this package. No substantive Lean work was begun in Stage 4.
