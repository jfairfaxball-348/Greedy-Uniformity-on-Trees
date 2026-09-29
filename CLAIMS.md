# Claim ledger

Status vocabulary: **definition**, **proved-background**, **proved-informal**, **verified-derivation**, **computational-evidence**, **conjecture**, **open-target**, **audit-status**.

| ID | Claim | Status | Audit / evidence |
|---|---|---|---|
| M1 | Greedy scanning of any vertex order returns an inclusion-maximal independent set. | proved-background | Elementary deterministic fact; same model appears in classical greedy MIS/RSA literature. |
| M2 | Random-permutation greedy is equivalent in law to iid continuous priorities, or to repeatedly choosing uniformly from currently available vertices. | proved-background | Elementary order-restriction argument; matches IMIS/Gazmuri formulations. |
| R1 | For a finite graph \(G\), maximal independent set \(I\), and \(n=|V(G)|\), \(\Pr_G(I)=n^{-1}\sum_{v\in I}\Pr_{G-N[v]}(I\setminus\{v\})\). | **proved-informal** | Stage 3, Lemma 2 in proof/INFORMAL_PROOF.md. |
| R2 | For a disjoint union, greedy output probabilities factor over components and permutation fibres acquire the exact multinomial interleaving factor. | **proved-informal** | Stage 3, Lemma 3. |
| R3 | If \(g_G(I)\) counts permutations producing \(I\) and \(r_v=|V(G-N[v])|\), then \(g_G(I)=\sum_{v\in I}(n-1)!/r_v!\,g_{G-N[v]}(I\setminus\{v\})\). | **proved-informal** | Stage 3, Lemma 4. |
| P1 | A fixed maximal independent set \(I\) is the greedy output iff every outside vertex has an earlier-priority neighbour in \(I\); equivalently its probability is the integral in Lemma 5. | **proved-informal** | Stage 3, Lemma 5. |
| A | For every finite nonempty tree, \(b(T)=0\) iff \(T\cong K_1\) or \(K_2\). | **proved-informal / pending Stage-4 audit** | Complete structural proof in Stage 3. Diameter-end pendant-star reduction; \(r\ge2\) gives a marginal mismatch, \(r=1\) gives an explicit paired-set strict inequality. Not yet frozen for Lean until the final audit. |
| B1 | \(T_{k,l}\) has \(2^k+1\) maximal independent sets. | **proved-informal** | Direct structural enumeration in the Stage-3 proof. |
| B2 | \(p_c=2^{-k}\sum_j\binom{k}{j}/(l+2j+1)\) and each particular type-\(j\) non-centre set has \(q_j=(l+2j)/(2^k(l+2j+1))\). | **proved-informal** | Direct iid-priority argument; independently checked against recursion in 12 earlier cases. |
| B3 | With \(l=2^k-k\), \(b(T)>0\) and \(b(T)=O(\sqrt{k}/4^k)=O(\sqrt{\log n_k}/n_k^2)\) along \(n_k=2^k+k+1\). | **proved-informal / pending Stage-4 audit** | Exact expectation identity and moment bound in Stage 3; no optimality or all-\(n\) claim. |
| E1 | There are 436 nonisomorphic unlabeled trees on 1–11 vertices. | computational-evidence | Generator counts match OEIS A000055 exactly. |
| E2 | Exactly \(K_1,K_2\) are uniform among those 436 trees. | computational-evidence | Exact rational recursion; independently brute-forced on all 25 tree classes through 7 vertices. |
| E3 | The minimum positive biases for \(n=3,\ldots,11\) are \(1/6,1/12,1/15,1/10,1/30,17/480,16/315,25/576,29/1260\). | computational-evidence | Exact rational census; no general extremal conclusion. |
| E4 | The Stage-3 local proof certificates hold on all 434 nonisomorphic trees of orders 3–11: 9 diameter-2 stars, 200 multi-leaf cases, 225 one-leaf cases, and 1103 exact paired-set inequalities. | computational-evidence | experiments/stage3_targeted.py; targeted verification of proof lemmas, not a substitute for them. |
| C | Determine \(a_n=\min\{b(T):|V(T)|=n\}\), sharp bounds, or structural minimizers. | **open-target / unresolved** | Not needed for the Stage-3 theorem package and not cleared to the same depth as A+B. |
| N1 | A+B constitute a plausibly substantive project if A needs a genuine structural proof. | audit-status | Stage-2 verdict **PASS FOR PROOF** on 2026-09-29. Stage 3 produced such a structural proof; Stage 4 must re-audit the actual theorem. |
| N2 | The process, RSA interpretation, and flat-vs-dynamical blocked-state contrast are themselves novel. | **false as a novelty claim** | Prior art includes Gazmuri/RSA and Edwards-vs-dynamical discussions. Do not claim these as contributions. |

## Current boundary

Stage 3 is complete at the informal-proof level. The exact obstruction A and companion construction B are now proved informally, but **neither is frozen as a novelty-cleared final theorem until Stage 4**. No Lean formalisation, Palomar registration, research paper, or arXiv submission has begun.
