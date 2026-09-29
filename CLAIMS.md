# Claim ledger

Status vocabulary: **definition**, **proved-background**, **verified-derivation**, **computational-evidence**, **conjecture**, **open-target**, **audit-status**.

| ID | Claim | Status | Audit / evidence |
|---|---|---|---|
| M1 | Greedy scanning of any vertex order returns an inclusion-maximal independent set. | proved-background | Elementary deterministic fact; same model appears in classical greedy MIS/RSA literature. |
| M2 | Random-permutation greedy is equivalent in law to repeatedly choosing uniformly from currently available vertices. | proved-background | Elementary restriction-of-random-permutation argument; matches IMIS/Gazmuri formulations. |
| A | For a nonempty tree, (b(T)=0) iff (T=K_1) or (K_2). | **conjecture / plausibly-new target** | Exact census through 11 vertices supports it. No checked source settles the converse. Closest 2026 Prop. 3.8 is sufficient only. |
| B1 | (T_{k,l}) has (2^k+1) maximal independent sets. | verified-derivation | Direct structural enumeration. |
| B2 | (p_c=(1/2^k)sum_jinom{k}{j}/(l+2j+1)) and each particular type-(j) non-centre set has (q_j=(l+2j)/(2^k(l+2j+1))). | verified-derivation | Direct iid-priority argument; independently checked against recursion in 12 cases. |
| B3 | With (l=2^k-k), (b(T)>0) and (b(T)=O(sqrt{k}/4^k)=O(sqrt{log n_k}/n_k^2)) along (n_k=2^k+k+1). | verified-derivation / plausibly-new | Exact expectation identity plus elementary moment bound. No optimality or all-n claim. |
| E1 | There are 436 nonisomorphic unlabeled trees on 1–11 vertices. | computational-evidence | Generator counts match OEIS A000055 exactly. |
| E2 | Exactly (K_1,K_2) are uniform among those 436 trees. | computational-evidence | Exact rational recursion; independently brute-forced on all 25 tree classes through 7 vertices. |
| E3 | The minimum positive biases for n=3..11 are (1/6,1/12,1/15,1/10,1/30,17/480,16/315,25/576,29/1260). | computational-evidence | Exact rational census; no general extremal conclusion. |
| C | Determine (a_n=min{b(T): |T|=n}), sharp bounds, or structural minimizers. | **open-target / unresolved** | No direct prior theorem found, but this target has not been frozen or cleared to the same depth as A+B. |
| N1 | A+B constitute a plausibly substantive project if A needs a genuine structural proof. | audit-status | **PASS FOR PROOF** on 2026-09-29, with bounded novelty uncertainty. |
| N2 | The process, RSA interpretation, and flat-vs-dynamical blocked-state contrast are themselves novel. | **false as a novelty claim** | Prior art includes Gazmuri/RSA and Edwards-vs-dynamical discussions. Do not claim these as contributions. |

## Current boundary

The project has **not** proved A, frozen the final theorem, begun Lean formalisation, registered with Palomar, written the paper, or submitted to arXiv. Stage 2 authorizes proof research only.
