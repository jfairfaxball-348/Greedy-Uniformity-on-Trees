# Roadmap

The project follows this fixed sequence.

1. **Scaffold repository — COMPLETE (2026-09-29).**
2. **Detailed prior-art and novelty audit — COMPLETE (2026-09-29).** Verdict: **PASS FOR PROOF** with bounded novelty uncertainty.
3. **Prove the selected theorem — COMPLETE INFORMALLY (2026-09-29).** A complete structural proof establishes \(G_T=U_T\) iff \(T\cong K_1\) or \(K_2\), and proves the mixed-spider near-uniform construction.
4. **Final prior-art/uniqueness check against the theorem actually proved — COMPLETE (2026-09-29).** Verdict: **PASS — FREEZE FOR FORMALISATION.** A and B are each classified as **plausibly new with bounded uncertainty**. The audit found no equivalent theorem, routine corollary, stronger checked characterization, or mixed-spider construction that subsumes the frozen package. Standard proof ingredients were explicitly separated from contribution-level claims.
5. **Formalise the frozen theorem in Lean — IN PROGRESS (partial checkpoint 3, 2026-09-29).** Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` remain pinned. The finite-law bridge is complete. The generic maximal-independent-set factor-two count, pendant decomposition, marginal counting bridge, three-order symmetry, multiple-pendant-leaf obstruction, and diameter-end pendant-star structure for Frozen Theorem A are now implemented. A new `GreedyUniformity/OneLeaf.lean` contains the local paired-set foundations for the exactly-one-pendant-leaf case; its strict fibre comparison and the final assembly/base cases of A remain to be completed. Frozen Theorem B remains untouched. The final Stage-5 state still requires the full A+B proof, final axiom inspection, and a clean reproducible build with no sorry, admit, project-specific axioms, or native_decide.
6. Complete Palomar registration under then-current requirements, distinguishing preparation, submission and confirmed registration.
7. Write the research paper around the audited theorem and the actual proof/formalisation boundary.
8. Complete arXiv submission under then-current requirements, distinguishing submission from public announcement.

Stage 5 has reached a partial third checkpoint but is not complete. Stages 6–8 have not begun. The exact finite-law bridge and most of Frozen Theorem A's structural/counting infrastructure are implemented; the one-leaf strict fibre comparison, final A assembly/base cases, and all of Frozen B remain.
