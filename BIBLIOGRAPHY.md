# Working bibliography

All entries below were relevant to the tree project. The separate poset/deletion-bias direction from the discovery note is intentionally omitted.

## Random greedy maximal independent sets

1. **Michael Krivelevich, Tamás Mészáros, Peleg Michaeli, Clara Shikhelman.** “Greedy maximal independent sets via local limits.” arXiv:1907.07216; later *Random Structures & Algorithms*.  
   https://arxiv.org/abs/1907.07216  
   Same random-permutation greedy MIS model; emphasis on size/density, local limits, graph sequences and trees.

2. **Alice Contat.** “Surprising identities for the greedy independent set on Cayley trees.” arXiv:2103.03800.  
   https://arxiv.org/abs/2103.03800  
   Exact law for the **size** of the greedy independent set on a **uniform Cayley tree**.

3. **P. G. Gazmuri.** “Independent sets in random sparse graphs.” *Networks* 14 (1984), 367–377.  
   Classical source for the greedy deletion algorithm on random sparse graphs; cited and described explicitly by Dall'Asta–Pin–Ramezanpour.

## Exact/asymptotically uniform iterative construction

4. **Ivan Kryven, Rik Versendaal, Mike de Vries.** “Unified framework for asymptotically uniform iterative construction of generalised random graphs with local constraints.” arXiv:2608.07239v1 (2026).  
   https://arxiv.org/abs/2608.07239  
   Key checked locations: Definition 3.6 (IMIS), Definition 3.7 (regular independent sets), Proposition 3.8 (sufficient exact uniformity condition), Definition 3.13 (2-uniformity), Theorem 3.23 (classification).

## Random sequential adsorption / parking / blocked states

5. **H. G. Dehling, S. R. Fleurke, C. Külske.** “Parking on a Random Tree.” *Journal of Statistical Physics* 133 (2008), 151–157. arXiv:0711.4061.  
   https://arxiv.org/abs/0711.4061  
   Blocking RSA on random-degree infinite trees; parking constants/occupation probabilities.

6. **Aidan W. Sudbury.** “Random sequential adsorption on random trees.” *Journal of Statistical Physics* 136 (2009), 51–58.  
   Fixed/random tree comparisons for occupation probabilities.

7. **M. D. Penrose, A. Sudbury.** “Exact and approximate results for deposition and annihilation processes on graphs.” *Annals of Applied Probability* 15 (2005), 853–889.  
   General deposition/RSA background on graphs, cited by the tree-parking literature.

8. **Luca Dall'Asta, Paolo Pin, Abolfazl Ramezanpour.** “Statistical Mechanics of maximal independent sets.” *Physical Review E* 80 (2009); arXiv:0907.3309.  
   https://arxiv.org/abs/0907.3309  
   Maximal independent sets as constrained/blocked states; explicit Edwards-measure vs dynamical-measure discussion; Section V.1 describes Gazmuri's greedy MIS algorithm and studies density/large deviations on random graph ensembles.

## Well-covered graphs and possible structural tools

9. **G. Ravindra.** “Well-covered graphs.” *Journal of Combinatorics, Information and System Sciences* 2 (1977), 20–21.  
   Classical characterization whose tree corollary says a tree is well-covered iff it is (K_1) or a corona of a tree (equivalently, a nontrivial well-covered tree has a perfect matching of pendant edges).

10. **Vadim E. Levit, Eugen Mandrescu.** “Well-covered trees.” *Congressus Numerantium* (1999).  
    Later treatment/reformulation of Ravindra's tree characterization.

## Enumeration reference

11. **OEIS A000055.** “Number of trees with n unlabeled nodes.”  
    https://oeis.org/A000055  
    Used only to validate the nonisomorphic-tree class counts through 11 vertices.

## Discovery record

12. **Independent_Combinatorics_Directions_2026-09-28.md.** User Library discovery note, dated 2026-09-28.  
    Treated as a preliminary lead document, not a proof or novelty certificate.

## Stage-4 additions and rechecks

13. **Nicholas Pippenger.** “Random Sequential Adsorption on Graphs.” *SIAM Journal on Discrete Mathematics* 2(3) (1989), 393–401. DOI 10.1137/0402034.  
    Exact random-sequence blocking process on graphs; occupation probabilities and jamming limits, not complete terminal-set equiprobability.

14. **Maximilien Gadouleau, David C. Kutner.** “Generalising the maximum independent set algorithm via Boolean networks.” *Information and Computation* 303 (2025), 105266. DOI 10.1016/j.ic.2025.105266.  
    Same deterministic greedy MIS map from the empty set; Example 1.1 explicitly gives the \(P_3\) permutation split. Main results concern reachability/fixing words and permutations, not random-output uniformity.

15. **Yair Caro, M. N. Ellingham, J. E. Ramey.** “Local Structure When All Maximal Independent Sets Have Equal Weight.” *SIAM Journal on Discrete Mathematics* 11(4) (1998), 644–654. DOI 10.1137/S0895480196300479.  
    “Weight” means the sum of assigned vertex weights; this is well-covered/weighted-well-covered theory, not equal probability under a greedy process.

16. **Bruce E. Sagan, Vincent R. Vatter.** “Maximal and maximum independent sets in graphs with at most r cycles.” *Journal of Graph Theory* 53(4) (2006), 283–314. arXiv:math/0505048. DOI 10.1002/jgt.20186.  
    Proposition 1.7 gives the standard maximal-independent-set “m-bound” \(m(G)\le m(G-v)+m(G-N[v])\), relevant background for Stage-3 Lemma 6.

17. **François Zara.** “Graphes Lies aux Espaces Polaires.” *European Journal of Combinatorics* 5(3) (1984), 255–290. DOI 10.1016/S0195-6698(84)80008-6.  
    Structural classification under maximal-clique axioms A1/A2; cited by Kryven–Versendaal–de Vries in their proof of Theorem 3.23 after complementation. Not a random-greedy-output theorem.

### 2026 preprint recheck

The Kryven–Versendaal–de Vries entry above was rechecked on 2026-09-29. arXiv:2608.07239 still had only v1 (submitted 2026-08-07). Definition 3.6, Definition 3.7, Proposition 3.8, Definition 3.13 and Theorem 3.23 remain the decisive locations; Proposition 3.8 is still a sufficient condition and no checked converse was found.
