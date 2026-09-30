# Stage 3 informal proof

**Project:** Greedy Uniformity on Trees  
**Stage:** 3 of 8  
**Date:** 2026-09-29  
**Status:** complete informal proof of the selected exact-obstruction theorem, together with the companion near-uniform construction. The theorem is **not frozen for formalisation** until Stage 4 completes the final prior-art/uniqueness audit.

## 1. Model and theorem package

Let \(T\) be a finite nonempty simple undirected tree. Give its vertices iid continuous priorities \(U_v\sim{\rm Unif}(0,1)\) and scan in increasing priority, selecting a vertex iff no previously selected neighbour has been selected. This is equivalent to scanning a uniformly random permutation.

Write \(\mathcal M(T)\) for the set of maximal independent sets, \(G_T\) for the greedy output law, and \(U_T\) for the uniform law on \(\mathcal M(T)\). Define
\[
b(T)=\frac12\sum_{I\in\mathcal M(T)}
\left|G_T(I)-\frac1{|\mathcal M(T)|}\right|.
\]

### Theorem A — exact obstruction on trees

For every finite nonempty tree \(T\),
\[
G_T=U_T
\quad\Longleftrightarrow\quad
T\cong K_1\text{ or }K_2.
\]
Equivalently, \(b(T)=0\) iff \(T\cong K_1\) or \(K_2\).

### Theorem B — explicit positive biases tending to zero

Let \(T_{k,l}\) have a centre \(c\), \(k\) arms \(c-u_i-v_i\) of length two, and \(l\) additional leaves adjacent to \(c\). Put \(N=2^k\). Then \(T_{k,l}\) has \(N+1\) maximal independent sets. The unique centre-containing set has probability
\[
p_c=\frac1N\sum_{j=0}^k\binom{k}{j}\frac1{l+2j+1},
\]
and each particular non-centre maximal independent set containing exactly \(j\) inner vertices \(u_i\) has probability
\[
q_j=\frac{l+2j}{N(l+2j+1)},
\]
with multiplicity \(\binom{k}{j}\).

For \(l=2^k-k\), let \(A=2^k+1\), \(J\sim{\rm Bin}(k,1/2)\), and \(W=2J-k\). Then
\[
b(T_{k,2^k-k})
=\frac12\left(
\mathbb E\frac{W^2}{A^2(A+W)}
+\mathbb E\frac{|W|}{A(A+W)}
\right)>0,
\]
and, for \(n_k=2^k+k+1\),
\[
b(T_{k,2^k-k})
=O\!\left(\frac{\sqrt{k}}{4^k}\right)
=O\!\left(\frac{\sqrt{\log n_k}}{n_k^2}\right).
\]
No all-\(n\) extremal or optimality statement is claimed.

## 2. Foundational recurrences and fibre counts

### Lemma 1 — greedy outputs are maximal independent sets

For every finite graph and every scan order, the selected set is independent by construction. Every rejected vertex had a selected neighbour when it was scanned, and selected vertices remain selected, so every unselected vertex is adjacent to the final selected set. Hence the output is maximal independent.

### Lemma 2 — first-vertex probability recurrence

Let \(G\) be a finite graph on \(n>0\) vertices and let \(I\) be a maximal independent set. Then
\[
\Pr_G(I)
=\frac1n\sum_{v\in I}
\Pr_{G-N[v]}(I\setminus\{v\}).
\tag{2.1}
\]
The probability on the empty graph is \(1\) for the empty target.

**Proof.** Condition on the first vertex of the uniformly random permutation. The first vertex is always selected, so output \(I\) is impossible if it lies outside \(I\). If the first vertex is \(v\in I\), then \(v\) is selected and every vertex of \(N(v)\) is permanently blocked. Rejected vertices never affect later decisions, so after deleting \(N[v]\) the process is exactly the process driven by the restriction of the remaining permutation to \(G-N[v]\), whose relative order is uniform. Finally \(I\setminus\{v\}\) is maximal in \(G-N[v]\): any residual vertex outside \(I\) was dominated in \(G\) by some member of \(I\), and if its only such member were \(v\) then it would lie in \(N(v)\) and not be residual. Summing over first vertices gives (2.1). \(\square\)

### Lemma 3 — component factorisation and interleaving

Let \(H\) be the disjoint union of components \(C_1,\ldots,C_s\), with \(n_i=|V(C_i)|\) and \(n=\sum_i n_i\). If \(J\in\mathcal M(H)\) and \(J_i=J\cap V(C_i)\), then
\[
\Pr_H(J)=\prod_{i=1}^s\Pr_{C_i}(J_i).
\tag{2.2}
\]
If \(g_H(J)\) is the number of vertex permutations of \(H\) whose greedy output is \(J\), then
\[
g_H(J)=\binom{n}{n_1,\ldots,n_s}\prod_{i=1}^s g_{C_i}(J_i).
\tag{2.3}
\]

**Proof.** Fix one successful relative order inside each component. A global permutation is obtained by interleaving those component orders, and every interleaving preserves the componentwise greedy outcomes because components do not interact. There are \(\binom{n}{n_1,\ldots,n_s}\) interleavings. This proves (2.3); division by \(n!\) gives (2.2). \(\square\)

### Lemma 4 — exact integer fibre recurrence

Let \(G,I,n\) be as in Lemma 2. For \(v\in I\), put
\[
r_v=|V(G-N[v])|.
\]
Then
\[
g_G(I)
=\sum_{v\in I}
\frac{(n-1)!}{r_v!}\,
g_{G-N[v]}(I\setminus\{v\}).
\tag{2.4}
\]
If the components of \(G-N[v]\) are \(C_{v,1},\ldots,C_{v,s_v}\) of sizes \(n_{v,i}\), then equivalently
\[
g_G(I)
=\sum_{v\in I}
\frac{(n-1)!}{\prod_i n_{v,i}!}
\prod_i g_{C_{v,i}}(I\cap V(C_{v,i})).
\tag{2.5}
\]
Consequently the greedy law is uniform on \(\mathcal M(G)\) iff \(g_G(I)\) is constant over all \(I\in\mathcal M(G)\).

**Proof.** Fix \(v\in I\) as the first vertex. Once \(v\) is selected, only the relative order of the \(r_v\) residual vertices matters; the \(n-1-r_v\) blocked neighbours of \(v\) may be inserted arbitrarily in the suffix. Each fixed residual order has
\[
\binom{n-1}{r_v}(n-1-r_v)!=\frac{(n-1)!}{r_v!}
\]
full suffix extensions. Summing successful residual orders proves (2.4). Substituting Lemma 3 gives (2.5). The final statement follows because all \(n!\) permutations are equiprobable. \(\square\)

## 3. Priority certificate

### Lemma 5 — local priority certificate

Let \(G\) be a finite graph, give each vertex an iid continuous priority \(U_v\), and let \(I\in\mathcal M(G)\). The greedy output is exactly \(I\) iff
\[
\forall w\notin I,\qquad
U_w>\min\{U_u:u\in I\cap N(w)\}.
\tag{3.1}
\]
In particular,
\[
\Pr_G(I)=
\int_{[0,1]^I}
\prod_{w\notin I}
\left(1-\min_{u\in I\cap N(w)}t_u\right)\,dt_I.
\tag{3.2}
\]

**Proof.** Necessity is immediate: if the final selected set is \(I\), each \(w\notin I\) was rejected by a previously selected neighbour, necessarily in \(I\).

For sufficiency, assume (3.1) and suppose some outside vertex is selected. Let \(w\notin I\) be the earliest-priority selected outside vertex. By (3.1), some \(u\in I\cap N(w)\) has \(U_u<U_w\). If \(u\) were rejected it would have an even earlier selected neighbour; since \(I\) is independent, that neighbour would lie outside \(I\), contradicting the choice of \(w\). Thus \(u\) was selected before \(w\), so \(w\) would be rejected, a contradiction. Hence no outside vertex is selected, and then every vertex of \(I\) is accepted because \(I\) is independent.

For (3.2), condition on the priorities of vertices in \(I\). Constraints for distinct outside vertices involve distinct independent outside priorities, so their conditional probabilities multiply. \(\square\)

Every maximal independent set therefore has positive greedy probability: put all vertices of \(I\) before all vertices outside it.

## 4. Structural counting lemmas

Write \(m(H)=|\mathcal M(H)|\), with \(m(\varnothing)=1\).

### Lemma 6 — deleting one vertex changes the maximal-set count by at most a factor two

For every finite graph \(H\) and every vertex \(z\),
\[
m(H)\le 2m(H-z).
\tag{4.1}
\]

**Proof.** Partition \(\mathcal M(H)\) according to whether \(z\) is present. Maximal independent sets excluding \(z\) are maximal in \(H-z\), so there are at most \(m(H-z)\) of them. Maximal independent sets containing \(z\), after deleting \(z\), are in bijection with \(\mathcal M(H-N[z])\).

It remains to prove \(m(H-N[z])\le m(H-z)\). For each \(J\in\mathcal M(H-N[z])\), extend \(J\) to some maximal independent set \(\widehat J\) of \(H-z\). This choice can be made independently for every \(J\). The resulting map is injective: because \(J\) is maximal in \(H-N[z]\), any maximal extension \(K\) in \(H-z\) satisfies
\[
K\cap V(H-N[z])=J.
\]
Thus two distinct \(J\)'s cannot yield the same \(K\). Hence \(m(H-N[z])\le m(H-z)\), and (4.1) follows. \(\square\)

### Lemma 7 — a diameter endpoint exposes a pendant star

Let \(T\) be a tree of diameter \(d\ge3\), and let
\[
v_0v_1\cdots v_d
\]
be a diameter path. Put \(y=v_1\) and \(z=v_2\). Then every neighbour of \(y\) other than \(z\) is a leaf. Thus \(y\) has \(r\ge1\) leaf neighbours and exactly one nonleaf neighbour \(z\).

If a tree has diameter \(2\), it is a star.

**Proof.** The endpoint \(v_0\) is a leaf. If a neighbour \(w\ne z\) of \(y\) were nonleaf, then in the component beyond \(w\) there would be a leaf \(a\) with \({\rm dist}(a,y)\ge2\). The path from \(a\) through \(y,z,\ldots,v_d\) would then have length at least \(2+(d-1)=d+1\), contradicting the definition of \(d\). The diameter-2 statement follows because every vertex is within distance one of the middle vertex of a diameter path. \(\square\)

## 5. Local imbalance at a diameter end

Let \(L\) be the set of leaf neighbours of \(y\) from Lemma 7 and let \(r=|L|\). Remove \(L\cup\{y\}\); the remaining component containing \(z\) is \(R\). Put
\[
F=R-z=T-N[y].
\]
Maximal independent sets containing \(y\) are exactly
\[
\{y\}\cup A,\qquad A\in\mathcal M(F),
\tag{5.1}
\]
so there are \(m(F)\). Maximal independent sets excluding \(y\) must contain every leaf of \(L\), and are exactly
\[
L\cup B,\qquad B\in\mathcal M(R),
\tag{5.2}
\]
so there are \(m(R)\).

### Lemma 8 — two or more pendant leaves force a marginal mismatch

If \(r\ge2\), then the greedy law on \(T\) is not uniform on maximal independent sets.

**Proof.** If \(y\) is greedily selected, then \(y\) must precede every leaf in \(L\): any earlier leaf is selected immediately and blocks \(y\). Therefore
\[
\Pr_G(y\text{ selected})\le\frac1{r+1}.
\tag{5.3}
\]
When the nonleaf neighbour \(z\) exists, this inequality is strict. Indeed, the positive-probability event that the permutation begins \(z,y\) and puts all leaves of \(L\) later has \(y\) earliest among \(L\cup\{y\}\), but \(z\) is already selected and blocks \(y\).

Under the uniform law on maximal independent sets, (5.1)-(5.2) give
\[
\Pr_U(y\in I)=\frac{m(F)}{m(F)+m(R)}.
\tag{5.4}
\]
Lemma 6 applied to \((R,z)\) gives \(m(R)\le2m(F)\), hence
\[
\Pr_U(y\in I)\ge\frac13.
\tag{5.5}
\]
Thus, when \(z\) exists and \(r\ge2\),
\[
\Pr_G(y\text{ selected})
<\frac1{r+1}\le\frac13\le\Pr_U(y\in I),
\]
so the laws have different marginals.

If no nonleaf neighbour exists, \(T\) is a star with centre \(y\). Its only maximal independent sets are \(\{y\}\) and \(L\), so the uniform marginal of \(y\) is \(1/2\), whereas greedily \(y\) is selected iff it is first among all \(r+1\) vertices, with probability \(1/(r+1)<1/2\). \(\square\)

### Lemma 9 — one pendant leaf gives a strict paired-set imbalance

Assume the diameter is at least \(3\) and \(r=1\). Let the unique leaf neighbour of \(y\) be \(x\), so locally \(x-y-z\) and \(\deg(y)=2\). Put
\[
R=T-\{x,y\},\qquad F=R-z=T-N[y].
\]
For every \(A\in\mathcal M(F)\), define
\[
I_y=\{y\}\cup A.
\]
Define a second maximal independent set by
\[
I_x=
\begin{cases}
\{x\}\cup A,&\text{if \(A\) contains a neighbour of \(z\) in \(R\)},\\
\{x,z\}\cup A,&\text{otherwise}.
\end{cases}
\tag{5.6}
\]
Then \(I_y,I_x\in\mathcal M(T)\) and their exact permutation fibres have different cardinalities; hence their greedy probabilities are strictly different.

**Proof.** The set \(I_y\) is maximal because \(A\) is maximal in \(F\) and \(y\) dominates \(x,z\). If \(A\) dominates \(z\), then \(A\) itself is maximal in \(R\), so \(\{x\}\cup A\) is maximal in \(T\). If \(A\) does not dominate \(z\), then \(A\cup\{z\}\) is independent and maximal in \(R\), so \(\{x,z\}\cup A\) is maximal in \(T\).

Let \(\sigma\) be the transposition swapping \(x\) and \(y\), and for a vertex order \(\ell\) write \(\sigma\ell\) for the order obtained by applying \(\sigma\) entrywise. Because \(\sigma\) is a permutation of the vertex set, \(\ell\mapsto\sigma\ell\) is injective on the finite set of all vertex orders. The finite priority-certificate characterization of greedy output is used only to verify that the following fibre maps preserve the claimed target; the comparison itself is a strict finite fibre-count argument.

**Case 1: \(A\) dominates \(z\).** Here \(I_x=\{x\}\cup A\). Swapping \(x\) and \(y\) sends every order in the fibre of \(I_x\) to an order in the fibre of \(I_y\):
\[
\sigma\bigl(\operatorname{fibre}(I_x)\bigr)
\subseteq \operatorname{fibre}(I_y).
\tag{5.7}
\]
Indeed, the certificate for \(I_x\) transfers under the swap: the unique obstruction involving the pendant leaf \(x\) becomes the corresponding obstruction involving \(y\), while vertices of \(A\subseteq F\) are fixed by \(\sigma\).

The inclusion is strict. Since \(I_y\) is maximal and \(y\in I_y\), \(z\notin I_y\), and \(yz\) is an edge, there is an order
\[
\ell=y,z,\ldots
\]
in the fibre of \(I_y\). After swapping \(x\) and \(y\), the order begins \(x,z,\ldots\). The pendant leaf \(x\) is not adjacent to \(z\), so both \(x\) and then \(z\) are greedily selected. Hence \(\sigma\ell\) cannot lie in the fibre of \(I_x=\{x\}\cup A\), which does not contain \(z\). Because \(\sigma\) is an involution, this shows that \(\ell\) is not in the image of the fibre of \(I_x\). Therefore
\[
|\operatorname{fibre}(I_x)|
<
|\operatorname{fibre}(I_y)|.
\tag{5.8}
\]

**Case 2: \(A\) does not dominate \(z\).** Here \(I_x=\{x,z\}\cup A\). In the reverse direction, swapping \(x\) and \(y\) sends every order in the fibre of \(I_y\) into the fibre of \(I_x\):
\[
\sigma\bigl(\operatorname{fibre}(I_y)\bigr)
\subseteq \operatorname{fibre}(I_x).
\tag{5.9}
\]
Again this is checked by transporting the finite priority certificate. Since \(A\) does not dominate \(z\), the target after the swap contains \(z\), and the remaining target vertices in \(A\) are fixed.

This inclusion is also strict. Since \(I_x\) is maximal and contains \(z\) but not \(y\), there is an order
\[
\ell=z,y,\ldots
\]
in the fibre of \(I_x\). Its swapped order begins \(z,x,\ldots\), so \(z\) is selected immediately. It therefore cannot lie in the fibre of \(I_y=\{y\}\cup A\), which excludes \(z\). By involutivity of \(\sigma\), \(\ell\) is missing from the image of the fibre of \(I_y\). Thus
\[
|\operatorname{fibre}(I_y)|
<
|\operatorname{fibre}(I_x)|.
\tag{5.10}
\]

In either case the two maximal independent sets have unequal permutation-fibre cardinalities. Since all vertex orders are equally likely, their greedy probabilities are unequal. \(\square\)

## 6. Proof of Theorem A

If \(T=K_1\), there is one maximal independent set, so the law is trivially uniform.

If \(T=K_2\), the two maximal independent sets are the two singletons. The first vertex in the random permutation is selected and blocks the other, so each singleton has probability \(1/2\).

Now suppose \(|V(T)|\ge3\) and choose a diameter path.

- If the diameter is \(2\), \(T\) is a star with at least two leaves, and Lemma 8 gives nonuniformity.
- If the diameter is at least \(3\), Lemma 7 gives a support vertex \(y\) with \(r\ge1\) leaf neighbours and exactly one nonleaf neighbour.
  - If \(r\ge2\), Lemma 8 gives a greedy-vs-uniform marginal mismatch at \(y\).
  - If \(r=1\), Lemma 9 produces two maximal independent sets with distinct greedy probabilities.

Therefore no tree on at least three vertices has uniform greedy terminal law. Together with the two base cases, this proves Theorem A. \(\square\)

No induction is used in the proof of Theorem A, so there is no unstated induction hypothesis. The earlier possible route “uniform greedy law implies well-covered” is unnecessary and is not claimed.

## 7. Proof of Theorem B

Fix \(k,l\ge1\) and put \(N=2^k\).

A maximal independent set containing the centre \(c\) is forced to contain every outer endpoint \(v_i\), and contains no inner endpoint \(u_i\) or direct leaf. Hence there is exactly one centre-containing maximal set.

If \(c\) is absent, every direct leaf must be selected and each arm contributes exactly one of \(u_i,v_i\). Hence there are exactly \(N\) non-centre maximal independent sets, for \(N+1\) total.

Ignore \(c\) temporarily. On each arm the earlier of \(u_i,v_i\) is selected, independently across arms, so any prescribed arm pattern has probability \(1/N\). Suppose the prescribed pattern contains exactly \(j\) inner vertices \(u_i\). Conditional on the \(k\) required pair orders, reinserting \(c\) changes the non-centre pattern precisely when \(c\) is selected. This happens exactly when \(c\) precedes all \(l\) direct leaves and, on each of the \(j\) inner-selected arms, precedes \(u_i\). Because the conditioning includes \(u_i<v_i\), this is equivalent to \(c\) being first among the \(l+2j+1\) vertices consisting of \(c\), the \(l\) leaves, and both endpoints of those \(j\) arms. Conditional on the pair orders, this has probability \(1/(l+2j+1)\). Therefore a particular type-\(j\) non-centre set has probability
\[
q_j=\frac1N\left(1-\frac1{l+2j+1}\right)
=\frac{l+2j}{N(l+2j+1)}.
\]
There are \(\binom{k}{j}\) such patterns. Summing the complementary centre-selected probabilities gives
\[
p_c=\frac1N\sum_{j=0}^k\binom{k}{j}\frac1{l+2j+1}.
\]

Now set \(l=N-k\), \(A=N+1\), \(J\sim{\rm Bin}(k,1/2)\), and \(W=2J-k\). For a type-\(J\) non-centre set,
\[
q_J-\frac1A=\frac{W}{NA(A+W)}.
\tag{7.1}
\]
Also
\[
p_c=\mathbb E\frac1{A+W}.
\]
Since \(\mathbb EW=0\),
\[
p_c-\frac1A
=-\mathbb E\frac{W}{A(A+W)}
=\mathbb E\frac{W^2}{A^2(A+W)}.
\tag{7.2}
\]
The right-hand side is positive because \(W\) is nonzero with positive probability. Summing the absolute deviations, and using the multiplicities \(\binom{k}{j}\) to convert the type sum into expectation under \(J\), gives
\[
b(T_{k,N-k})
=\frac12\left(
\mathbb E\frac{W^2}{A^2(A+W)}
+\mathbb E\frac{|W|}{A(A+W)}
\right)>0.
\]
Because \(W\ge-k\), \(A+W\ge A-k\); also \(\mathbb EW^2=k\) and \(\mathbb E|W|\le\sqrt{k}\). Hence
\[
b(T_{k,N-k})
\le\frac12\left(
\frac{k}{A^2(A-k)}
+\frac{\sqrt{k}}{A(A-k)}
\right)
=O\!\left(\frac{\sqrt{k}}{4^k}\right).
\]
Finally \(n_k=N+k+1\) satisfies \(N\le n_k\le2N\) for \(k\ge1\), while \(k=\log_2N=O(\log n_k)\). Therefore
\[
b(T_{k,N-k})
=O\!\left(\frac{\sqrt{\log n_k}}{n_k^2}\right).
\]
This proves Theorem B. \(\square\)

## 8. Dependency map

- **Lemma 1:** deterministic greedy maximality.
- **Lemma 2:** first-vertex conditioning.
- **Lemma 3:** component interleaving/factorisation.
- **Lemma 4:** Lemmas 2–3 plus exact suffix counting.
- **Lemma 5:** priority-order certificate; independent of Lemmas 2–4.
- **Lemma 6:** finite maximal-independent-set counting.
- **Lemma 7:** tree diameter structure.
- **Lemma 8:** Lemmas 6–7 plus the support/leaf order observation.
- **Lemma 9:** Lemma 7 plus the residual-forest pairing, the finite priority-certificate/output equivalence, and strict injections between exact permutation fibres induced by swapping the pendant leaf with its support vertex.
- **Theorem A:** Lemmas 7–9 plus direct \(K_1,K_2\) checks. Lemmas 2–4 are not required for the shortest proof, but supply the requested recurrence/fibre framework and are useful for later formalisation.
- **Theorem B:** iid-priority representation, direct arm decomposition, and elementary binomial moment bounds.

## 9. Proof status and boundaries

**Proved informally in Stage 3:**

1. The exact obstruction Theorem A for every finite nonempty tree.
2. The exact first-vertex probability recurrence.
3. The exact component factorisation and permutation-fibre interleaving formula.
4. The explicit mixed-spider probabilities and positive vanishing-bias subsequence Theorem B.

**Not claimed:**

- worldwide originality or priority of A or B;
- an all-\(n\) formula or sharp bound for \(a_n=\min_{|V(T)|=n}b(T)\);
- optimality of the mixed-spider construction;
- Lean verification;
- Palomar registration;
- a paper or arXiv submission.

Stage 4 must audit the theorem actually proved before its statement is frozen for formalisation.
