# Claim ledger

Status vocabulary: **definition**, **proved-background**, **proved-informal**, **frozen-for-formalisation**, **verified-derivation**, **computational-evidence**, **conjecture**, **open-target**, **audit-status**.

| ID | Claim | Status | Audit / evidence |
|---|---|---|---|
| M1 | Greedy scanning of any vertex order returns an inclusion-maximal independent set. | proved-background | Elementary deterministic fact; same model appears in classical greedy MIS/RSA literature. |
| M2 | Random-permutation greedy is equivalent in law to iid continuous priorities, or to repeatedly choosing uniformly from currently available vertices. | proved-background | Standard random-order/iid-label/RSA/IMIS formulations; rechecked against KMMSh, Pippenger and Kryven–Versendaal–de Vries. |
| R1 | For a finite graph \(G\), maximal independent set \(I\), and \(n=|V(G)|\), \(\Pr_G(I)=n^{-1}\sum_{v\in I}\Pr_{G-N[v]}(I\setminus\{v\})\). | **proved-informal** | Stage 3, Lemma 2. Elementary first-choice conditioning; not a standalone novelty claim. |
| R2 | For a disjoint union, greedy output probabilities factor over components and permutation fibres acquire the exact multinomial interleaving factor. | **proved-informal** | Stage 3, Lemma 3. Elementary component independence/interleaving; not a standalone novelty claim. |
| R3 | If \(g_G(I)\) counts permutations producing \(I\) and \(r_v=|V(G-N[v])|\), then \(g_G(I)=\sum_{v\in I}(n-1)!/r_v!\,g_{G-N[v]}(I\setminus\{v\})\). | **proved-informal** | Stage 3, Lemma 4. Counting form of first-choice conditioning; exact prior statement not located, but treated as elementary rather than contribution-level novelty. |
| P1 | A fixed maximal independent set \(I\) is the greedy output iff every outside vertex has an earlier-priority neighbour in \(I\); equivalently its probability is the integral in Lemma 5. | **proved-informal** | Stage 3, Lemma 5. Standard iid-priority representation plus an elementary fixed-output certificate; no standalone novelty claim. |
| M3 | For every finite graph \(H\) and vertex \(z\), \(m(H)\le2m(H-z)\). | **proved-informal / background-level** | Stage 3, Lemma 6. Sagan–Vatter Proposition 1.7 gives \(m(H)\le m(H-z)+m(H-N[z])\); the factor-two form follows from the Stage-3 injection \(m(H-N[z])\le m(H-z)\). |
| A | For every finite nonempty tree, \(b(T)=0\) iff \(T\cong K_1\) or \(K_2\). | **proved-informal / frozen-for-formalisation** | Complete Stage-3 structural proof. Stage-4 audit verdict: **plausibly new with bounded uncertainty**; no equivalent theorem, converse to KVD Prop. 3.8, or stronger checked graph characterization was found. |
| B1 | \(T_{k,l}\) has \(2^k+1\) maximal independent sets. | **proved-informal / frozen-for-formalisation** | Direct structural enumeration in Stage 3. |
| B2 | \(p_c=2^{-k}\sum_j\binom{k}{j}/(l+2j+1)\) and each particular type-\(j\) non-centre set has \(q_j=(l+2j)/(2^k(l+2j+1))\). | **proved-informal / frozen-for-formalisation** | Direct iid-priority argument; independently checked against recursion in 12 cases. Stage-4 exact-formula searches found no collision. |
| B3 | With \(l=2^k-k\), \(b(T)>0\) and \(b(T)=O(\sqrt{k}/4^k)=O(\sqrt{\log n_k}/n_k^2)\) along \(n_k=2^k+k+1\). | **proved-informal / frozen-for-formalisation** | Exact expectation identity and moment bound in Stage 3. Stage-4 classification: **plausibly new with bounded uncertainty**. No optimality or all-\(n\) claim. |
| E1 | There are 436 nonisomorphic unlabeled trees on 1–11 vertices. | computational-evidence | Generator counts match OEIS A000055 exactly. |
| E2 | Exactly \(K_1,K_2\) are uniform among those 436 trees. | computational-evidence | Exact rational recursion; independently brute-forced on all 25 tree classes through 7 vertices. |
| E3 | The minimum positive biases for \(n=3,\ldots,11\) are \(1/6,1/12,1/15,1/10,1/30,17/480,16/315,25/576,29/1260\). | computational-evidence | Exact rational census; no general extremal conclusion. |
| E4 | The Stage-3 local proof certificates hold on all 434 nonisomorphic trees of orders 3–11: 9 diameter-2 stars, 200 multi-leaf cases, 225 one-leaf cases, and 1103 exact paired-set inequalities. | computational-evidence | experiments/stage3_targeted.py; targeted verification of proof lemmas, not a substitute for them. |
| C | Determine \(a_n=\min\{b(T):|V(T)|=n\}\), sharp bounds, or structural minimizers. | **open-target / unresolved** | Optional future direction only. It is not part of the frozen Stage-5 theorem and has not received the same theorem-level audit. |
| N1 | The proved A+B package is substantive enough to proceed to formalisation. | audit-status | **Stage-4 verdict: PASS — FREEZE FOR FORMALISATION (2026-09-29).** A supplies the all-tree necessity theorem; B supplies a quantitative connected-tree near-uniform sequence. |
| N2 | The process, RSA interpretation, flat-vs-dynamical blocked-state contrast, elementary recurrences, or maximal-set counting bound are themselves novel. | **false as a novelty claim** | Classical/random-greedy/RSA literature and Sagan–Vatter background. Do not claim these as contributions. |
| N3 | The checked literature establishes worldwide priority for A or B. | **false as a certainty claim** | The audit supports only **plausibly new with bounded uncertainty**. Negative search results are not a uniqueness certificate. |

## Current boundary

Stages 1–4 are complete. The exact A+B package above is **frozen for Stage 5**. Theorem A and Theorem B are both classified by the final audit as plausibly new with bounded uncertainty; no collision or narrowing was required.

No Lean formalisation, Palomar registration, research paper, or arXiv submission has begun. Stage 5 must formalise the frozen statements without silently strengthening them. In particular, do not add an all-\(n\) extremal or optimality theorem, and do not claim the unproved implication “uniform greedy law implies well-covered”.
