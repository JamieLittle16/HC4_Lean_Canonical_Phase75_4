# Phase 75.15.1 — Source-collision compile fixes

This patch is a compile-only repair of `CanonicalSmithDefectExposureCollision.lean`.

Changes:

1. Replaces two brittle cast-heavy `omega` proofs of one-step section legality with the already-certified wall arithmetic lemmas
   `alignedSmithSectionValueFour_nonnegative` and
   `alignedSmithSectionValueTwo_nonnegative`.
2. Proves the one-step wall inequality by rewriting the defining `if` directly, matching the already-green proof style in `SeparatedSmithBoundaryClosure`.
3. Replaces two underspecified parenthesized `by` expressions in the transformed special-point proofs by explicitly typed intermediate equalities.

No theorem statements, definitions, assumptions, or mathematical content are changed.
