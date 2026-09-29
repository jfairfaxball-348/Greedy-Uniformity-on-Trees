# Roadmap

The project follows this fixed sequence.

1. **Scaffold repository — COMPLETE (2026-09-29).**
2. **Detailed prior-art and novelty audit — COMPLETE (2026-09-29).** Verdict: **PASS FOR PROOF** with bounded novelty uncertainty.
3. **Prove the selected theorem — COMPLETE INFORMALLY (2026-09-29).** A complete structural proof establishes \(G_T=U_T\) iff \(T\cong K_1\) or \(K_2\), and proves the mixed-spider near-uniform construction.
4. **Final prior-art/uniqueness check against the theorem actually proved — COMPLETE (2026-09-29).** Verdict: **PASS — FREEZE FOR FORMALISATION.** A and B are each classified as **plausibly new with bounded uncertainty**. The audit found no equivalent theorem, routine corollary, stronger checked characterization, or mixed-spider construction that subsumes the frozen package. Standard proof ingredients were explicitly separated from contribution-level claims.
5. **Formalise the frozen theorem in Lean — NEXT.** Formalise exactly A+B as frozen in CLAIMS.md and HANDOVER.md, with pinned Lean/Mathlib versions, a reproducible build, axiom inspection, and no sorry, admit, project-specific axioms, or native_decide in the final proof chain.
6. Complete Palomar registration under then-current requirements, distinguishing preparation, submission and confirmed registration.
7. Write the research paper around the audited theorem and the actual proof/formalisation boundary.
8. Complete arXiv submission under then-current requirements, distinguishing submission from public announcement.

Stages 5–8 have not been completed or represented as complete. No substantive Stage-5 Lean work was begun during Stage 4.
