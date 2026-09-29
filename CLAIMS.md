# Claim ledger

Status vocabulary: **definition**, **proved-background**, **derived-and-checked**, **computational-evidence**, **conjecture**, **open-target**, **audit-status**.

| ID | Claim | Status | Evidence / caveat |
|---|---|---|---|
| M1 | Greedy scanning of any vertex order returns an inclusion-maximal independent set. | proved-background | Elementary deterministic fact; to be cited/proved when the paper is written. |
| A | For a nonempty tree, b(T)=0 iff T is K1 or K2. | conjecture | Exhaustive exact computation through 11 vertices only; no general proof yet. |
| B1 | The mixed spider T_{k,l} has 2^k+1 maximal independent sets. | derived-and-checked | Direct structural argument and exact computation. |
| B2 | For T_{k,l}, p_c and q_j are given by the project formulas. | derived-and-checked | Direct random-priority argument; checked independently against recursion in 12 cases. |
| B3 | With l=2^k-k, the bias is positive and tends to zero with O(sqrt(k)/4^k). | derived-and-checked | Algebra from B2 plus elementary moment bounds; full proof belongs to stage 3 if selected. |
| E1 | There are 436 nonisomorphic unlabeled trees on 1–11 vertices. | computational-evidence | Counts 1,1,1,2,3,6,11,23,47,106,235; external census source to be logged in audit. |
| E2 | Exactly K1 and K2 are uniform among those 436 trees. | computational-evidence | Exact rational recursion; independently brute-forced on all 25 nonisomorphic trees through 7 vertices. |
| C | Determine a_n=min{b(T): |T|=n}. | open-target | No optimality claim is made for the mixed-spider family. |
