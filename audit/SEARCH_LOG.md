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
