# Palomar Stage-6 package

This file records both the repository-side Palomar preparation and the final
registration outcome.

## Registration record

- Palomar ID: `PALOMAR-2026-10-01-000003`
- Version: **1**
- Status: **registered**
- Trust level: **high**
- Published: **2026-10-01T00:28:54Z**
- Immutable source commit: `1733c29a5165148d71a2f0bd1ed2dcd7c35309ce`
- Preserved archive: `PalomarArchive/jfairfaxball-348--Greedy-Uniformity-on-Trees--0c04ff5c5faa`
- Public entry: https://palomar-registry.org/entry.html?id=PALOMAR-2026-10-01-000003&version=1

The registry record contains all nine intended theorem declarations: the two
final Theorem A declarations and all seven final Theorem B checkpoints.

## Submission unit

- Repository: `jfairfaxball-348/Greedy-Uniformity-on-Trees`
- Selected project: repository root
- Comparator configuration: `comparator.json`
- Metadata: `formalization.yaml`
- Challenge: `GreedyUniformity/PalomarChallenge.lean`
- Solution: `GreedyUniformity/PalomarSolution.lean`
- Compared declarations: the two final Frozen A declarations and all seven
  final Frozen B checkpoints
- Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`
- Novelty wording: **plausibly new with bounded uncertainty**

## Palomar compatibility migration

Current PalomarSubmission commit
`65f0154ed776cd26c224254aa57b379137f28b0d` requires the Lean module system
and a Lean toolchain at or above v4.35.0-rc2. The Stage-5 snapshot used Lean
v4.34.1, so Stage 6 ports the repository to Lean v4.35.0-rc3 and matching
Mathlib commit `c55e6e786f49471c72fbddbec5415808896aec1e`.

This migration is solely to satisfy current Palomar packaging. The frozen
Theorem A and B statements were not strengthened or reopened. After removing
only the module/public-visibility scaffolding, the final `TheoremA.lean` and
`TheoremB.lean` sources agree with their Stage-5 versions.

Every committed project `.lean` file now uses Lean's module system and stays
within Palomar's source-size limits.

## Comparator surface

`comparator.json` compares all nine final theorem declarations. It also lists

    GreedyUniformity.mixedSpiderNoncenterSet

under `definition_names`. The Mathlib-only Challenge states the intended
finite-set definition explicitly, and the Solution uses the corresponding
proof-development definition. Separate compilation produced non-identical
elaborated bodies for this one definition, so the Palomar-supported definition
hole is used narrowly: Comparator checks its type and safety and the verifier
checks the Solution-side body for permitted axioms, while all nine theorem
statements are still compared exactly. No other project definition is a
Comparator definition hole.

## Mechanical preflight

The caller workflow `.github/workflows/palomar-preflight.yml` pins the reusable
Palomar verifier and its `pipeline_commit` to the same upstream commit
`65f0154ed776cd26c224254aa57b379137f28b0d`, uses `mode: full`, and selects
`palomar-standard-v1`.

A full predictive preflight has passed for the finished package content,
including Challenge provenance, the complete Solution build, Comparator,
permitted-axiom enforcement, con-ron, NanoDa, and Lean's default kernel. The
final registration commit must be the exact commit from a green full preflight;
the session handover supplies that SHA and report digest.

A passing preflight does **not** perform Palomar editorial review, create a
Palomar identifier, preserve source tags, or register the result.

## Manual registration fields

For a new browser submission use:

- repository: `jfairfaxball-348/Greedy-Uniformity-on-Trees`
- commit: the exact 40-character SHA from the final green preflight
- selected project: repository root / leave blank when the form represents root by blank
- Comparator configuration path: `comparator.json`
- formalization metadata path: default `formalization.yaml` / leave blank when the form uses the default
- existing Palomar ID: blank (new registration)
- authorization relationship: `I am a responsible author or maintainer` **only if you can personally and truthfully affirm it**
- authorization evidence: optional for a responsible author/maintainer submitting their own work

The browser sign-in route establishes repository write access separately from
the authorship/maintainer declaration.

## Licence choice

The repository previously had no root licence. The Stage-6 package uses
Apache-2.0, matching `project.license` in `formalization.yaml` and the
current official Palomar template. This is a legal/publication choice for the
responsible human maintainer: review it before registration. If a different
licence is desired, change both `LICENSE` and `project.license` and rerun
the full preflight before submitting.

## Remaining boundary

The package is prepared, mechanically preflighted, and **registered** as
`PALOMAR-2026-10-01-000003` version 1 from immutable source commit
`1733c29a5165148d71a2f0bd1ed2dcd7c35309ce`. Stage 6 is complete. Stage 7
paper writing is now the next permitted stage; Stage 8 remains blocked until
the fixed workflow reaches it.
