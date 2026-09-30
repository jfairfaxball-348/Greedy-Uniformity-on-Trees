# Roadmap

The project follows this fixed sequence.

1. **Scaffold repository — COMPLETE (2026-09-29).**
2. **Detailed prior-art and novelty audit — COMPLETE (2026-09-29).** Verdict: **PASS FOR PROOF** with bounded novelty uncertainty.
3. **Prove the selected theorem — COMPLETE INFORMALLY (2026-09-29).** A complete structural proof establishes (G_T=U_T) iff (T\cong K_1) or (K_2), and proves the mixed-spider near-uniform construction.
4. **Final prior-art/uniqueness check against the theorem actually proved — COMPLETE (2026-09-29).** Verdict: **PASS — FREEZE FOR FORMALISATION.** A and B are each classified as **plausibly new with bounded uncertainty**. Standard proof ingredients are separated from contribution-level claims.
5. **Formalise the frozen theorem in Lean — COMPLETE (2026-09-30).** The Stage-5 A+B package was verified under Lean 4.34.1 / Mathlib `d13f23b723b8a846827a245b89c10fc7d3f11612`. GitHub Actions run **#161** at `47802b8a18a92847e447e88c02ecb42620b3da09` passed the complete root build, forbidden-placeholder rejection, and **5** Python tests. All final A and B `#print axioms` checkpoints reported exactly `[propext, Classical.choice, Quot.sound]`.
6. **Complete Palomar registration — IN PROGRESS (2026-09-30).** Repository-side packaging is **PREPARED** and the dedicated current Palomar `mode: full` preflight has **PASSED**. Current Palomar policy forced a format-only migration to Lean 4.35.0-rc3 / Mathlib `c55e6e786f49471c72fbddbec5415808896aec1e` and the Lean module system; the frozen theorem statements were not strengthened. The package uses `formalization.yaml`, `comparator.json`, `GreedyUniformity/PalomarChallenge.lean`, `GreedyUniformity/PalomarSolution.lean`, and Apache-2.0. **Actual Palomar registration is still pending the responsible user's browser submission and receipt of a Palomar identifier.**
7. **Write the research paper — NOT STARTED.** Blocked until Stage 6 registration is actually complete.
8. **Complete arXiv submission — NOT STARTED.** Blocked until the workflow reaches Stage 8; distinguish submission from public announcement.

The novelty wording remains **plausibly new with bounded uncertainty**. Do not
reopen the frozen A+B mathematics except for a narrowly targeted correction
genuinely forced by integration or discovered verification evidence. Do not
mark Stage 6 complete until an actual Palomar registration identifier has been
received and recorded.
