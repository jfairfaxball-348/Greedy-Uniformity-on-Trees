# Roadmap

The project follows this fixed sequence.

1. **Scaffold repository — COMPLETE (2026-09-29).**
2. **Detailed prior-art and novelty audit — COMPLETE (2026-09-29).** Verdict: **PASS FOR PROOF** with bounded novelty uncertainty.
3. **Prove the selected theorem — COMPLETE INFORMALLY (2026-09-29).** A complete structural proof establishes \(G_T=U_T\) iff \(T\cong K_1\) or \(K_2\), and proves the mixed-spider near-uniform construction.
4. **Final prior-art/uniqueness check against the theorem actually proved — COMPLETE (2026-09-29).** Verdict: **PASS — FREEZE FOR FORMALISATION.** A and B are each classified as **plausibly new with bounded uncertainty**. The audit found no equivalent theorem, routine corollary, stronger checked characterization, or mixed-spider construction that subsumes the frozen package. Standard proof ingredients were explicitly separated from contribution-level claims.
5. **Formalise the frozen theorem in Lean — IN PROGRESS (Frozen A checkpoint complete, 2026-09-29).** Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` remain pinned. Frozen Theorem A is now fully formalised: finite-law bridge, maximal-independent-set counting, pendant decomposition, multi-leaf obstruction, finite one-leaf strict fibre comparison, diameter-end tree structure, the ≥3-vertex obstruction, the one/two-vertex base cases, and the exact `K_1`/`K_2` graph-isomorphism statements. Run #84 passed `lake build`, placeholder rejection, and `4 passed` Python tests. `#print axioms` for both final A statements gives only `propext`, `Classical.choice`, and `Quot.sound`. Frozen Theorem B remains untouched. The final Stage-5 state still requires Frozen B plus its final verification/axiom inspection.
6. Complete Palomar registration under then-current requirements, distinguishing preparation, submission and confirmed registration.
7. Write the research paper around the audited theorem and the actual proof/formalisation boundary.
8. Complete arXiv submission under then-current requirements, distinguishing submission from public announcement.

Stage 5 has reached the completed Frozen-Theorem-A checkpoint but is not complete because Frozen Theorem B remains. Stages 6–8 have not begun. Do not reopen A except for a narrowly targeted correction genuinely forced by later integration.
