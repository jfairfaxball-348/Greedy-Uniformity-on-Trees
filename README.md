# Greedy Uniformity on Trees

Research repository for the distribution of random greedy maximal independent sets on finite trees.

## Current status

**All eight stages are complete. The frozen A+B theorem package is registered with Palomar as `PALOMAR-2026-10-01-000003` (version 1, high trust), from immutable source commit `1733c29a5165148d71a2f0bd1ed2dcd7c35309ce`. The publication manuscript remains `paper/main.tex`; the self-contained arXiv upload bundle is `arxiv/` at bundle commit `14b3c6ecbbf423eebefa8f673124793f3e3f3c02` and passed clean TeX Live 2023/BibTeX preflight plus PDF inspection before submission. The paper is now live as [`arXiv:2610.02276`](https://arxiv.org/abs/2610.02276), version 1, submitted 2026-10-01 in `math.CO` with `math.PR` secondary. The arXiv-issued DataCite DOI is [`10.48550/arXiv.2610.02276`](https://doi.org/10.48550/arXiv.2610.02276), and the recorded submission licence is CC BY 4.0.**

Stage 2 gave PASS FOR PROOF, not a priority certificate. Stage 3 produced the complete informal proof. Stage 4 then re-audited the **actual proved theorem and proof shape** against current primary literature. The final classification is deliberately bounded: both A and B are **plausibly new with bounded uncertainty**, not “definitely novel” or “unique worldwide”.

The closest source remains Kryven–Versendaal–de Vries (arXiv:2608.07239v1). Their Definition 3.6 is the same finite IMIS law, and Proposition 3.8 gives a sufficient exact-uniformity condition (regular independent sets), but the checked paper states no converse. Its Theorem 3.23 classifies the stronger 2-uniform class and therefore does not make the tree obstruction routine.

## Model

Choose a uniformly random permutation of the vertices of a finite nonempty simple undirected tree, scan it once, and select a vertex iff it has no previously selected neighbour. The output is an inclusion-maximal independent set.

For a tree (T), let (G_T) be the greedy output law and (U_T) uniform on its maximal independent sets (mathcal M(T)). Define
[
b(T)=\frac12\sum_{I\in\mathcal M(T)}
\left|G_T(I)-\frac1{|\mathcal M(T)|}\right|.
]

## Frozen theorem package

- **A — exact obstruction:** for every finite nonempty tree (T),
  [
  G_T=U_T\iff T\cong K_1\text{ or }K_2,
  ]
  equivalently (b(T)=0) iff (T\cong K_1) or (K_2).

- **B — explicit near-uniform connected trees:** for the mixed spider (T_{k,l}), Stage 3 gives exact probabilities (p_c) and (q_j). Under the tuning (l=2^k-k),
  [
  0<b(T_{k,2^k-k})
  =O(\sqrt{k}/4^k)
  =O(\sqrt{\log n_k}/n_k^2),
  \qquad n_k=2^k+k+1,
  ]
  together with the exact expectation identity recorded in `proof/INFORMAL_PROOF.md` and `HANDOVER.md`.

There is no all-(n) or optimality claim. The extremal problem (a_n=\min_{|V(T)|=n}b(T)) remains optional/open and is not part of the frozen target.

## Proof and audit boundary

The proof of A is tree-structural. At a diameter endpoint, the support vertex has a pendant star and at most one nonleaf neighbour. Two or more pendant leaves force a greedy-vs-uniform marginal mismatch. Exactly one pendant leaf yields a canonical pair of maximal independent sets with strictly unequal greedy probabilities.

Stage 4 deliberately does **not** claim novelty for the process, iid-priority/RSA formulation, elementary first-choice/fibre recurrences, the maximal-independent-set count bound, or diameter-end tree geometry. New Stage-4 sources include Gadouleau–Kutner (2025), whose Example 1.1 already displays the unequal (P_3) permutation fibres, and Sagan–Vatter (2006), whose Proposition 1.7 supplies a standard maximal-set counting bound. Neither source subsumes A.

See `audit/PRIOR_ART_NOVELTY_AUDIT.md` and `audit/SEARCH_LOG.md` for the complete final audit.

## Reproducibility

The Stage-5 theorem package was originally completed under **Lean 4.34.1** and Mathlib commit `d13f23b723b8a846827a245b89c10fc7d3f11612` (Mathlib tag `v4.34.1`), with GitHub Actions run **#161** at `47802b8a18a92847e447e88c02ecb42620b3da09` passing the complete A+B root build, forbidden-placeholder rejection, and the Python suite (**5 passed**).

Current Palomar policy requires Lean's module system and a toolchain at or above v4.35.0-rc2, so Stage 6 performed a packaging-only compatibility port. The repository is now pinned to **Lean 4.35.0-rc3** and Mathlib commit `c55e6e786f49471c72fbddbec5415808896aec1e` (tag `v4.35.0-rc3`). The exact dependency graph is committed in `lake-manifest.json`.

The Palomar package is:

- `formalization.yaml` — structured provenance, classification, production/review metadata and public abstract;
- `comparator.json` — the two final A declarations plus all seven final B checkpoints;
- `GreedyUniformity/PalomarChallenge.lean` — Mathlib-only statement surface;
- `GreedyUniformity/PalomarSolution.lean` — proof-development solution surface;
- `LICENSE` — Apache-2.0.

The dedicated full Palomar preflight uses the pinned PalomarSubmission workflow at commit `65f0154ed776cd26c224254aa57b379137f28b0d` with execution profile `palomar-standard-v1`. It has passed the Challenge provenance audit, complete Solution build, Comparator check, permitted-axiom enforcement, con-ron, NanoDa, and Lean default-kernel replay with no warnings or errors.

Lean build:

    lake build

Python regression suite:

    python -m pytest -q

The ordinary proof-source placeholder audit still rejects `sorry`, `admit`, and `native_decide`; the only excluded file is the intentional Palomar Challenge, whose theorem holes are validated by the Palomar Comparator against the proved Solution.

## Independence and integrity

This project is separate from **ProbStack — Random Stacking on Trees** and from TreeStack. No conclusion from those repositories is imported as evidence.

Lean formalisation, Palomar registration, the Stage-7 research manuscript, and Stage-8 arXiv submission are complete for the frozen A+B package. Palomar registration is **PALOMAR-2026-10-01-000003**, version 1, from immutable source commit `1733c29a5165148d71a2f0bd1ed2dcd7c35309ce`. The paper source is `paper/main.tex`; the verified Stage-8 upload bundle is `arxiv/` at commit `14b3c6ecbbf423eebefa8f673124793f3e3f3c02`; and the live publication record is [`arXiv:2610.02276`](https://arxiv.org/abs/2610.02276), v1, with DOI [`10.48550/arXiv.2610.02276`](https://doi.org/10.48550/arXiv.2610.02276) and CC BY 4.0 licence. The Stage-4 novelty status remains **plausibly new with bounded uncertainty**, and the frozen package must not be silently strengthened into all-(n), minimizer, optimality, matching-lower-bound, well-covered-converse, or worldwide-priority claims.

Start with `PROJECT_CHARTER.md`, `CLAIMS.md`, `audit/PRIOR_ART_NOVELTY_AUDIT.md`, `audit/SEARCH_LOG.md`, `proof/INFORMAL_PROOF.md`, `experiments/VERIFIED_RESULTS.md`, `PALOMAR_SUBMISSION.md`, and `HANDOVER.md`.
