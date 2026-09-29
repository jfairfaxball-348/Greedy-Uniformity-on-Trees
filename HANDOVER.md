# Stage-5 handover

**Date:** 2026-09-29  
**Completed:** Stage 1 (scaffold), Stage 2 (detailed pre-proof audit), Stage 3 (complete informal proof), Stage 4 (final theorem-level prior-art/uniqueness audit)  
**Stage-4 verdict:** **PASS — FREEZE FOR FORMALISATION**  
**Next:** Stage 5 only — formalise the frozen theorem package in Lean.  
**Not completed:** Stages 5–8.

No substantive Lean work was begun during Stage 4.

## Final audit classification

- **Theorem A:** **plausibly new with bounded uncertainty**.
- **Theorem B:** **plausibly new with bounded uncertainty**.
- No checked source states either theorem, makes A a routine corollary through a general graph characterization, or supplies the mixed-spider formula/tuning/rate.
- This is not a claim of worldwide uniqueness or priority.

The closest current source is Kryven–Versendaal–de Vries, arXiv:2608.07239v1. The arXiv record was rechecked on 2026-09-29 and still contained only v1. Definition 3.6 gives the same finite IMIS process; Proposition 3.8 proves **regular independent sets \(\Rightarrow\) uniform terminal IMIS**, but the checked text gives no converse. Definition 3.13 and Theorem 3.23 concern the stronger 2-uniform class, so that classification does not imply A.

Stage 4 also added two useful boundary sources. Gadouleau–Kutner (Information and Computation 303 (2025), 105266), Example 1.1, explicitly gives the \(P_3\) split of two permutations producing the middle singleton versus four producing the endpoint pair; their paper studies reachability/fixing words and permutations rather than random-output uniformity. Sagan–Vatter, Proposition 1.7, gives the standard maximal-independent-set count bound \(m(G)\le m(G-v)+m(G-N[v])\), so the Stage-3 counting lemma is background-level rather than a novelty claim.

## Exact frozen theorem A

Let \(T\) be any finite nonempty simple undirected tree. Choose a uniformly random permutation of \(V(T)\) and scan it once, selecting a vertex iff it has no previously selected neighbour. Let \(G_T\) be the law of the resulting maximal independent set and \(U_T\) the uniform law on \(\mathcal M(T)\).

Then
\[
G_T=U_T
\quad\Longleftrightarrow\quad
T\cong K_1\text{ or }K_2.
\]
Equivalently,
\[
b(T)=\frac12\sum_{I\in\mathcal M(T)}
\left|G_T(I)-\frac1{|\mathcal M(T)|}\right|=0
\quad\Longleftrightarrow\quad
T\cong K_1\text{ or }K_2.
\]

The complete informal proof is proof/INFORMAL_PROOF.md. The tree necessity proof is the diameter-end local obstruction from Lemmas 7–9; the earlier possible implication “uniform implies well-covered” is neither needed nor proved.

## Exact frozen theorem B

Let \(T_{k,l}\) have a centre \(c\), \(k\ge1\) arms
\[
c-u_i-v_i
\]
of length two, and \(l\ge0\) additional leaves adjacent to \(c\). Put \(N=2^k\).

There are \(N+1\) maximal independent sets. The unique centre-containing set has probability
\[
p_c=
\frac1N\sum_{j=0}^k
\binom{k}{j}\frac1{l+2j+1}.
\]

Each particular non-centre maximal independent set containing exactly \(j\) inner vertices \(u_i\) has probability
\[
q_j=
\frac{l+2j}{N(l+2j+1)},
\]
with multiplicity \(\binom{k}{j}\).

For
\[
l=2^k-k,
\qquad
A=2^k+1,
\qquad
J\sim{\rm Bin}(k,1/2),
\qquad
W=2J-k,
\]
we have
\[
b(T_{k,2^k-k})
=
\frac12
\left(
\mathbb E\frac{W^2}{A^2(A+W)}
+
\mathbb E\frac{|W|}{A(A+W)}
\right)>0.
\]

Writing
\[
n_k=2^k+k+1,
\]
the same family satisfies
\[
b(T_{k,2^k-k})
=
O\!\left(\frac{\sqrt{k}}{4^k}\right)
=
O\!\left(\frac{\sqrt{\log n_k}}{n_k^2}\right)
\qquad(k\to\infty).
\]

This is a subsequence construction only. **Do not add an all-\(n\), matching lower bound, minimizer characterization, or optimality claim.**

## Proof ingredients and novelty boundary for Stage 5

Formalisation may use the Stage-3 dependency map, but paper-level novelty claims must remain narrower:

1. deterministic maximality — background;
2. first-vertex recurrence — elementary conditioning;
3. component factorisation/interleaving — elementary;
4. integer permutation-fibre recurrence — elementary counting form of the recurrence;
5. iid-priority certificate/integral — direct use of the standard iid-priority representation;
6. \(m(H)\le2m(H-v)\) — background-level counting inequality; compare Sagan–Vatter Proposition 1.7;
7. diameter-end pendant-star structure — elementary tree geometry;
8. multi-leaf marginal obstruction — part of the project proof assembly;
9. one-leaf canonical paired-set inequality — part of the project proof assembly.

The final theorem, not every supporting lemma, is the contribution-level object under the audit.

## Stage-4 searches that mattered most

The final audit rechecked or added:

- Kryven–Versendaal–de Vries, Defs. 3.6, 3.7, 3.13; Prop. 3.8; Thm. 3.23; current arXiv version;
- Zara (1984), the classification source cited in the proof of KVD Thm. 3.23;
- Krivelevich–Mészáros–Michaeli–Shikhelman for the same random-order/iid-priority model and size/density focus;
- Pippenger (1989) for classical graph RSA;
- Dall'Asta–Pin–Ramezanpour for Gazmuri's algorithm and Edwards/dynamical blocked-state language;
- Gadouleau–Kutner (2025), especially Example 1.1;
- Caro–Ellingham–Ramey (1998) to separate “equal weight” from equal probability;
- Sagan–Vatter (2006), Proposition 1.7, for the maximal-set count recurrence/bound;
- targeted spider/starlike/subdivided-star, exact-formula, tuning, rate, equal-basin and complete-output-law searches.

No checked source supplied the A converse/classification or the B family/tuning/rate. Full details and negative-search caveats are in audit/PRIOR_ART_NOVELTY_AUDIT.md and audit/SEARCH_LOG.md.

## Stage-5 boundary

Stage 5 should formalise **exactly Frozen A and Frozen B** above using a pinned Lean/Mathlib environment and a reproducible build.

The formal proof chain should contain no sorry, admit, project-specific axioms, or native_decide. Axiom inspection should be recorded. Computation can support development but must not replace the theorem proof.

Do not begin Palomar registration, paper writing, or arXiv work before Stage 5 is completed under the fixed workflow.
