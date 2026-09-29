# Stage-2 search log

**Access date:** 2026-09-29 unless otherwise stated.

This log records what was actually checked. “No matching result located” means exactly that; it is not a uniqueness certificate.

## Discovery records

- `Independent_Combinatorics_Directions_2026-09-28.md` — found in the user Library. Read only the tree direction. It reports the same 1–11 census, the mixed-spider formula, and an explicitly preliminary first audit. Used as a lead list, not as authority.
- `Independent_Combinatorics_Experiments_2026-09-28.zip` — not located in the accessible conversation/Library search. Reconstructed the tree computations independently instead.

## Primary / close sources

### Krivelevich–Mészáros–Michaeli–Shikhelman
**Title:** *Greedy maximal independent sets via local limits*  
**arXiv:** https://arxiv.org/abs/1907.07216  
**Later publication:** Random Structures & Algorithms.  
**Checked:** model definition; iid-priority equivalence; stated “greedy independence ratio” focus; tree/random-tree discussion; later discussion of Contat/Panholzer size-law results.  
**Implication:** exact same greedy process, but the paper's target is output size/density and asymptotic graph sequences, not exact probabilities of complete maximal independent sets on a fixed tree.

### Contat
**Title:** *Surprising identities for the greedy independent set on Cayley trees*  
**arXiv:** https://arxiv.org/abs/2103.03800  
**Checked:** abstract/main result and scope.  
**Implication:** exact law for the **size** of the greedy independent set on a **uniform random Cayley tree**. Does not imply fixed-tree output equiprobability.

### Kryven–Versendaal–de Vries
**Title:** *Unified framework for asymptotically uniform iterative construction of generalised random graphs with local constraints*  
**arXiv:** https://arxiv.org/abs/2608.07239v1  
**Version checked:** v1, submitted 2026-08-07.  
**Exact locations checked:** Definition 3.6 (IMIS), Definition 3.7 (regular independent sets), Proposition 3.8, Definition 3.13 (2-uniformity), discussion immediately following Definition 3.13, Theorem 3.23 and the cited classification context.  
**Implication:** their IMIS is equivalent in law to the random-permutation process on a finite graph. Proposition 3.8 gives **regular independent sets => exact uniform terminal IMIS**, and also forces all MISs to be maximum. Applying regular-independent-set equality to singleton independent sets forces ordinary vertex regularity, excluding every connected nontrivial tree except (K_2). However the proposition is one-way; no checked converse says exact uniformity forces regular independent sets or 2-uniformity. Theorem 3.23 therefore does not settle the tree obstruction.

### Dall'Asta–Pin–Ramezanpour
**Title:** *Statistical Mechanics of maximal independent sets*  
**arXiv:** https://arxiv.org/abs/0907.3309  
**Checked:** introduction/background on blocked states and Edwards vs dynamical measure; Section V.1 on Gazmuri's algorithm.  
**Exact relevant location:** Section V.1 defines the algorithm by selecting a remaining vertex uniformly, assigning it occupied, deleting it and its neighbours, and iterating.  
**Implication:** the broad static-flat-vs-dynamical comparison and the greedy MIS process are prior art. Their quantitative work is on densities/large deviations in random graph ensembles, not exact fixed-tree terminal-set probabilities.

### Dehling–Fleurke–Külske
**Title:** *Parking on a Random Tree*  
**arXiv:** https://arxiv.org/abs/0711.4061  
**Journal:** J. Stat. Phys. 133 (2008), 151–157.  
**Checked:** abstract/model/references.  
**Implication:** “blocking RSA” / parking terminology on trees is established; result concerns parking constants/occupation probabilities on random-degree infinite trees.

### Sudbury
**Title:** *Random sequential adsorption on random trees*  
**Journal:** J. Stat. Phys. 136 (2009), 51–58.  
**Checked:** abstract and scope via institutional publication page.  
**Implication:** compares occupation probabilities on fixed and random trees; not full terminal-state law.

### Gazmuri
**Title:** *Independent sets in random sparse graphs*  
**Journal:** Networks 14 (1984), 367–377.  
**Checked through:** bibliographic/source trail in Dall'Asta–Pin–Ramezanpour and web metadata.  
**Implication:** establishes the older greedy-removal algorithm lineage on random sparse graphs; no fixed-tree uniform-output characterization located.

### Ravindra / well-covered trees
**Original result:** G. Ravindra, *Well-covered graphs*, J. Combinatorics, Information and System Sciences 2 (1977), 20–21.  
**Checked through:** later papers/surveys quoting the tree corollary.  
**Result used only as background:** a tree is well-covered iff it is (K_1) or a corona of a tree; equivalently, a nontrivial well-covered tree has a perfect matching of pendant edges.  
**Implication:** possible Stage-3 structural tool if uniform greedy law can be shown to imply well-coveredness. No such implication was found or assumed.

## Enumeration validation

**OEIS A000055:** https://oeis.org/A000055  
Checked sequence and definition “number of trees with n unlabeled nodes.” For n=1..11 the values are
(1,1,1,2,3,6,11,23,47,106,235), matching the generator exactly.

This verifies the expected number of isomorphism classes at each order; independent output-law checks are recorded in `experiments/VERIFIED_RESULTS.md`.

## Search families and synonym sweeps

The following query families were run in multiple combinations, including quoted and broadened forms:

- “random greedy maximal independent set” + distribution / law / uniform;
- “random permutation” + maximal independent set + uniform/equiprobable;
- “iterative maximal independent set” + uniformly random maximal independent set;
- “all maximal independent sets equally likely” + greedy;
- blocking random sequential adsorption + tree + jammed/blocked configuration;
- graph parking process + maximal independent set;
- Edwards measure + maximal independent sets + dynamical measure;
- uniform measure on maximal independent sets;
- hard-core model + maximal independent set (separated from uniform measure on **all** independent sets);
- total variation + greedy independent set;
- near-uniform / asymptotically uniform + greedy maximal independent set;
- spider graph / spider tree / starlike tree / subdivided star + greedy independent set;
- mixed length-one length-two arms + maximal independent set;
- well-covered trees + greedy/uniform.

### Negative-result record
No searched source stated:
1. the exact tree obstruction A;
2. a converse to Kryven–Versendaal–de Vries Proposition 3.8 sufficient for A;
3. the mixed-spider (T_{k,l}) formula in the present form;
4. the tuning (l=2^k-k) or the (O(sqrt{k}/4^k)) / (O(sqrt{log n}/n^2)) subsequence rate;
5. a sharp theorem for (a_n=min_{|T|=n}b(T)).

Again, these are bounded search outcomes, not proof of absence.

## Citation trails followed

- KMMSh -> older greedy MIS literature and random-tree size/density literature.
- Dall'Asta–Pin–Ramezanpour -> Gazmuri algorithm and blocked-state / Edwards-measure language.
- Dehling–Fleurke–Külske -> blocking RSA and earlier deposition/annihilation literature.
- Kryven–Versendaal–de Vries -> regular-independent-set and 2-uniform classification trail, including the older structural classification they cite. No checked cited statement was found to supply the missing converse for exact IMIS uniformity.

## Specific remaining gaps

- No exhaustive subscription-only MathSciNet/zbMATH search was completed.
- No author correspondence was attempted.
- The August 2026 preprint's citation network is recent and may grow; Stage 4 must recheck it.
- The unavailable discovery ZIP was not inspected, although its absence is not a mathematical blocker because all needed tree computations were independently reconstructed.
- C received a targeted search but not the same theorem-level clearance as A+B because no precise extremal conjecture beyond the definition of (a_n) has yet been frozen.

These gaps are why the verdict is “PASS FOR PROOF with bounded novelty uncertainty,” not “priority established.”

---

# Stage-4 search log

**Access date:** 2026-09-29.  
**Purpose:** final theorem-level audit after the Stage-3 proof. Negative entries mean only “no matching result located in the checked material”.

## Current-version recheck: Kryven–Versendaal–de Vries

**Ivan Kryven, Rik Versendaal, Mike de Vries.** *Unified framework for asymptotically uniform iterative construction of generalised random graphs with local constraints.* arXiv:2608.07239.

- Current arXiv record checked on 2026-09-29: still **v1**, submitted 2026-08-07.
- Definition 3.6: IMIS process, equivalent on a finite graph to the random-order greedy process in this project.
- Definition 3.7: regular independent sets.
- Proposition 3.8: regular independent sets imply equiprobable IMIS selection sequences and a uniform terminal MIS; it also implies all MISs are maximum.
- Definition 3.13: 2-uniformity is a stronger condition.
- Theorem 3.23: classification of 2-uniform graphs.
- No converse to Proposition 3.8 was located.
- No theorem stating that exact uniform IMIS output forces regular independent sets or 2-uniformity was located.

**Citation chase from Theorem 3.23:** François Zara, *Graphes Lies aux Espaces Polaires*, European Journal of Combinatorics 5 (1984), 255–290. Kryven–Versendaal–de Vries cite Section 7, Part A, especially Remark 7.7, for the \(\alpha\ge3\) classification after complementation. Zara's A1/A2 conditions fix maximal-clique size and the number of neighbours an outside vertex has in each maximal clique; this is not a greedy-output probability theorem.

## Same process / adjacent observables

**Krivelevich–Mészáros–Michaeli–Shikhelman.** *Greedy maximal independent sets via local limits.* Random Structures & Algorithms; DOI 10.1002/rsa.21200.  
Checked the model definition and iid-label equivalence. The stated program studies the greedy independence ratio and asymptotic size/density, including tree families. No fixed-tree complete-output equiprobability classification was located.

**Nicholas Pippenger.** *Random Sequential Adsorption on Graphs.* SIAM J. Discrete Math. 2 (1989), 393–401; DOI 10.1137/0402034.  
The abstract defines the same random-sequence blocking process. Results concern occupancy probabilities and jamming limits on regular/high-girth graphs and related models, not the probability of each complete maximal independent set.

**Dall'Asta–Pin–Ramezanpour.** *Statistical Mechanics of maximal independent sets.* arXiv:0907.3309 / Phys. Rev. E 80 (2009).  
Rechecked the blocked-state/Edwards-vs-dynamical discussion and Section V.1 (Gazmuri algorithm). The dynamic-vs-flat contrast and the greedy-removal algorithm are prior art; the quantitative targets are densities/large deviations on random graph ensembles.

## New close deterministic source

**Maximilien Gadouleau, David C. Kutner.** *Generalising the maximum independent set algorithm via Boolean networks.* Information and Computation 303 (2025), 105266; DOI 10.1016/j.ic.2025.105266.

Checked the publisher full text/abstract and introduction.

- Same deterministic MIS algorithm: start empty, visit vertices in an order, add a vertex iff no neighbour is already present.
- Example 1.1 treats \(P_3\): two permutations beginning at the middle vertex yield \(\{b\}\); the other four yield \(\{a,c\}\).
- Main results instead concern reachability from arbitrary initial states, fixing words, fixing permutations (“permises”), permissible graphs, and complexity.
- No random-permutation equiprobability characterization of graphs or trees was located.

This is a genuine proof-shape/example overlap and is now recorded, but it does not imply Theorem A.

## “Equal weight” terminology check

**Yair Caro, M. N. Ellingham, J. E. Ramey.** *Local Structure When All Maximal Independent Sets Have Equal Weight.* SIAM J. Discrete Math. 11 (1998), 644–654; DOI 10.1137/S0895480196300479.

The abstract defines weight as the sum of assigned vertex weights in an abelian group, with well-coveredness and parity as examples. This is not probability, number of greedy orderings, or basin size. It is a false positive for the phrase “all maximal independent sets have equal weight”.

## Maximal-independent-set counting recurrence

**Bruce E. Sagan, Vincent R. Vatter.** *Maximal and maximum independent sets in graphs with at most r cycles.* J. Graph Theory 53 (2006), 283–314; arXiv:math/0505048; DOI 10.1002/jgt.20186.

Checked Proposition 1.7 (“m-bound”):
\[
m(G)\le m(G-v)+m(G-N[v]).
\]
This places the Stage-3 maximal-set count lemma firmly in standard counting territory. The factor-two bound \(m(H)\le2m(H-v)\) is a short consequence once \(m(H-N[v])\le m(H-v)\) is supplied. No novelty is claimed for it.

## Proof-shape searches

Query families included combinations of:

- random greedy maximal independent set + uniform / equiprobable / law / distribution;
- random-order or random-permutation MIS + uniform maximal independent set;
- IMIS + converse / exact uniformity / regular independent sets;
- equal basin sizes / permutation fibres / number of greedy orderings;
- blocking RSA / parking / random sequential packing + finite tree / forest / jammed state;
- Edwards measure / flat measure / dynamical measure + maximal independent set;
- leaf / pendant / support / diameter endpoint + greedy independent set;
- probability of a prescribed maximal independent set + iid priorities / integral / recurrence;
- first-vertex recurrence + maximal independent set output;
- graph characterization + equiprobable greedy maximal independent sets.

No checked source gave the full tree obstruction, the Stage-3 leaf-support pairing argument, or a stronger theorem that made A immediate.

## Mixed-spider searches

Query families included:

- spider tree / starlike tree / subdivided star + greedy MIS / RSA / parking;
- mixed arms of lengths one and two + maximal independent set;
- near-uniform / almost uniform / asymptotically uniform + complete greedy MIS law;
- exact formula fragments involving \(l+2j+1\), \(2^k-k\), and \(\sqrt{k}/4^k\);
- total variation + greedy output + connected trees;
- stronger arbitrary-closeness constructions for connected trees.

No checked source contained the exact \(p_c,q_j\) formulas, tuning \(l=2^k-k\), Stage-3 expectation identity, or \(O(\sqrt{k}/4^k)=O(\sqrt{\log n}/n^2)\) subsequence rate. No stronger pre-existing connected-tree construction for total-variation closeness of the complete-output law was located.

Search hits saying greedy independent sets are “near optimal” or “arbitrarily close to optimal” concerned **cardinality/optimization**, not closeness to the uniform law on maximal independent sets.

## Stage-4 negative-result record

No checked source stated or routinely implied:

1. \(G_T=U_T\) for a finite tree iff \(T\cong K_1,K_2\);
2. a converse to Kryven–Versendaal–de Vries Proposition 3.8 sufficient to force (1);
3. a general exact-uniform-output graph characterization whose tree specialization is (1);
4. the mixed-spider formulas and tuning used in Theorem B;
5. the \(O(\sqrt{\log n}/n^2)\) connected-tree subsequence bound for complete-output total variation.

These are bounded search results, not a worldwide priority certificate.

## Stage-4 classification

- **Theorem A:** plausibly new with bounded uncertainty.
- **Theorem B:** plausibly new with bounded uncertainty.
- **Elementary recurrences, iid-priority reformulation, maximal-set count bound, and diameter-end geometry:** background/readily derivable; do not present as standalone novelty.
- **Stage-4 verdict:** **PASS — FREEZE FOR FORMALISATION.**
