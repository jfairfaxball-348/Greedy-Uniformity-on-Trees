# Palomar Stage-6 package

This file records repository-side preparation only. It is **not** evidence that
Palomar registration has occurred.

## Submission unit

- Repository: `jfairfaxball-348/Greedy-Uniformity-on-Trees`
- Selected project: repository root
- Comparator configuration: `comparator.json`
- Metadata: `formalization.yaml`
- Challenge: `Challenge.lean`
- Solution: `Solution.lean`
- Compared declarations: the two final Frozen A declarations and all seven
  final Frozen B checkpoints
- Permitted axioms: `propext`, `Classical.choice`, `Quot.sound`
- Novelty wording: **plausibly new with bounded uncertainty**

## Palomar compatibility migration

PalomarSubmission commit
`65f0154ed776cd26c224254aa57b379137f28b0d` requires the Lean module system and a Lean toolchain at or above
v4.35.0-rc2. The Stage-5 snapshot used Lean v4.34.1, so Stage 6 ports the
repository to Lean v4.35.0-rc3 and matching Mathlib commit
`c55e6e786f49471c72fbddbec5415808896aec1e`. This migration is solely to satisfy current Palomar packaging;
the frozen mathematical statements are not strengthened or reopened.

Every committed project `.lean` file was moved to the module/public-visibility
surface required by current Palomar policy.

## Mechanical preflight

The caller workflow `.github/workflows/palomar-preflight.yml` pins the reusable
Palomar verifier and its `pipeline_commit` to the same upstream commit
`65f0154ed776cd26c224254aa57b379137f28b0d`, uses `mode: full`, and selects
`palomar-standard-v1`.

A passing run means only that the predictive mechanical preflight passed for the
exact commit tested. It does not perform Palomar editorial review, create a
Palomar identifier, preserve source tags, or register the result.

## Licence choice

The repository previously had no root licence. The Stage-6 package uses
Apache-2.0, matching the current official Palomar template. This is a legal and
personal publication choice for the responsible human maintainer: review it
before registration. If a different licence is desired, change both `LICENSE`
and `project.license` and rerun the full preflight before submitting.
