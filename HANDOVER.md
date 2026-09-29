# Stage-4 handover

**Date:** 2026-09-29  
**Completed:** Stage 1 (scaffold), Stage 2 (detailed prior-art/novelty audit), Stage 3 (complete informal proof)  
**Next:** Stage 4 only — final prior-art/uniqueness audit against the theorem actually proved.  
**Not completed:** Stages 4–8.

## Exact theorem now proved informally

For every finite nonempty tree \(T\), the random-permutation greedy maximal-independent-set law is uniform on \(\mathcal M(T)\) iff
\[
T\cong K_1\quad\text{or}\quad K_2.
\]
Equivalently \(b(T)=0\) iff \(T\cong K_1\) or \(K_2\).

The companion theorem is also proved informally. For the mixed spider \(T_{k,l}\) with \(N=2^k\), the unique centre-containing set has probability
\[
p_c=\frac1N\sum_{j=0}^k\binom{k}{j}\frac1{l+2j+1},
\]
and each particular non-centre type-\(j\) set has
\[
q_j=\frac{l+2j}{N(l+2j+1)}.
\]
For \(l=2^k-k\), with \(A=2^k+1\), \(J\sim{\rm Bin}(k,1/2)\), \(W=2J-k\),
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
=O(\sqrt{k}/4^k)
=O(\sqrt{\log n_k}/n_k^2),
\qquad n_k=2^k+k+1.
\]
No all-\(n\) extremal or optimality claim is part of the theorem package.

## Proof architecture

The complete proof is in proof/INFORMAL_PROOF.md.

### Foundational exact identities

1. **First-vertex recurrence**
   \[
   \Pr_G(I)=\frac1{|V(G)|}\sum_{v\in I}\Pr_{G-N[v]}(I\setminus\{v\}).
   \]
2. **Component factorisation:** probabilities multiply over connected components; permutation fibres acquire the exact multinomial interleaving factor.
3. **Integer fibre recurrence:** if \(g_G(I)\) counts permutations producing \(I\) and \(r_v=|V(G-N[v])|\),
   \[
   g_G(I)=\sum_{v\in I}\frac{(n-1)!}{r_v!}g_{G-N[v]}(I\setminus\{v\}).
   \]
4. **Priority certificate:** a maximal independent set \(I\) is the output iff every outside vertex has an earlier-priority neighbour in \(I\).

### Structural obstruction

Choose a diameter endpoint and its support vertex \(y\).

- If the tree has diameter 2, it is a nontrivial star and is immediately biased.
- Otherwise \(y\) has \(r\ge1\) leaf neighbours and exactly one nonleaf neighbour \(z\).
- If \(r\ge2\), greedy selection of \(y\) has probability \(<1/(r+1)\le1/3\), whereas under the uniform maximal-set law its inclusion probability is at least \(1/3\). The latter uses the general count lemma \(m(H)\le2m(H-v)\).
- If \(r=1\), write the local path as \(x-y-z\) and \(F=T-N[y]\). For every \(A\in\mathcal M(F)\), pair \(I_y=\{y\}\cup A\) with:
  - \(I_x=\{x\}\cup A\) if \(A\) dominates \(z\); a direct priority integral gives \(\Pr(I_y)>\Pr(I_x)\);
  - \(I_x=\{x,z\}\cup A\) otherwise; a \(1/3\) versus at least \(2/3\) local comparison gives \(\Pr(I_x)>\Pr(I_y)\).

Thus every tree on at least three vertices has unequal greedy output probabilities or already has a marginal mismatch.

The earlier possible route “uniform implies well-covered implies corona” is **not needed** and should not be stated as a theorem.

## Dependency map

- Lemma 1: deterministic maximality.
- Lemma 2: first-vertex recurrence.
- Lemma 3: component interleaving/factorisation.
- Lemma 4: exact fibre recurrence from Lemmas 2–3.
- Lemma 5: iid-priority certificate.
- Lemma 6: \(m(H)\le2m(H-v)\).
- Lemma 7: diameter-end pendant-star structure.
- Lemma 8: multi-leaf marginal imbalance from Lemmas 6–7.
- Lemma 9: one-leaf paired-set strict inequality from Lemmas 5 and 7.
- Theorem A: Lemmas 7–9 plus direct \(K_1,K_2\) checks.
- Theorem B: direct priority decomposition plus binomial moment bounds.

## Targeted computations added in Stage 3

experiments/stage3_targeted.py checks only the local proof certificates, not a larger blind search. Through order 11 it checks all 434 nontrivial tree classes:

- 9 diameter-2 stars;
- 200 diameter-end cases with at least two pendant leaves;
- 225 diameter-end cases with exactly one pendant leaf;
- 1103 paired maximal-independent-set inequalities in the one-leaf cases.

The targeted test passes. The pre-existing 1–11 exact census and mixed-spider checks remain unchanged.

## Discrepancies / abandoned routes

No counterexample was found. The key revision is conceptual: the hoped-for intermediate implication “uniform greedy law implies well-covered” is unnecessary and was not proved. The final proof uses a direct diameter-end local obstruction.

A naive monotonicity heuristic based only on maximal-independent-set cardinality is false in small trees and is not used.

## Stage-4 task

Re-audit the **actual proved statements and proof shape**, especially:

1. exact uniformity of random greedy/IMIS terminal maximal independent sets on finite trees;
2. whether prior work gives the same leaf/diameter-end obstruction, a converse sufficient to imply it, or a broader characterization making it routine;
3. the exact permutation-fibre and priority-certificate formulations under possible alternative terminology;
4. the mixed-spider formulas, tuning \(l=2^k-k\), and \(O(\sqrt{\log n}/n^2)\) subsequence rate.

Do not freeze the theorem or begin Lean until this audit is complete. The Stage-2 closest source remains Kryven–Versendaal–de Vries (2026), whose checked Proposition 3.8 was sufficient rather than converse; Stage 4 must recheck the current version and surrounding references.
