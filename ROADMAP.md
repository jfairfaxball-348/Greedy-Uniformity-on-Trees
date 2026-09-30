# Roadmap

The project follows this fixed sequence.

1. **Scaffold repository — COMPLETE (2026-09-29).**
2. **Detailed prior-art and novelty audit — COMPLETE (2026-09-29).** Verdict: **PASS FOR PROOF** with bounded novelty uncertainty.
3. **Prove the selected theorem — COMPLETE INFORMALLY (2026-09-29).** A complete structural proof establishes \(G_T=U_T\) iff \(T\cong K_1\) or \(K_2\), and proves the mixed-spider near-uniform construction.
4. **Final prior-art/uniqueness check against the theorem actually proved — COMPLETE (2026-09-29).** Verdict: **PASS — FREEZE FOR FORMALISATION.** A and B are each classified as **plausibly new with bounded uncertainty**. Standard proof ingredients are separated from contribution-level claims.
5. **Formalise the frozen theorem in Lean — COMPLETE (2026-09-30).** Lean 4.34.1 and Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612` remain pinned. Frozen A and B are fully formalised in the exact finite permutation model. GitHub Actions run **#161** at `47802b8a18a92847e447e88c02ecb42620b3da09` passed the complete A+B root `lake build` (8954 jobs), forbidden-placeholder rejection, and **5** Python tests. All final A and B `#print axioms` checkpoints report exactly `[propext, Classical.choice, Quot.sound]`; there are no project-specific mathematical axioms or forbidden placeholders.
6. **Complete Palomar registration — NOT STARTED.** Use then-current requirements and distinguish preparation, submission, and confirmed registration.
7. **Write the research paper — NOT STARTED.** Base it on the audited theorem and the actual proof/formalisation boundary.
8. **Complete arXiv submission — NOT STARTED.** Use then-current requirements and distinguish submission from public announcement.

Stage 5 is complete. Stage 6 is next, but it has not begun. Do not reopen the frozen A+B mathematics except for a narrowly targeted correction genuinely forced by later integration or discovered verification evidence.
