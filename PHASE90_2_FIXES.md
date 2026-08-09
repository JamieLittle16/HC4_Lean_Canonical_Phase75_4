# Phase 90.2 — first binary Schur entry scale invariance

## New module

    HC4/Newton/FirstSchurEntry.lean

Phase 90.1 proves the pivot theorem for a nonzero determinant-zero symmetric
binary block. Phase 90.2 records the normalisation invariance required at an
actual first Schur coefficient.

For a scalar `t` and block `q`:

    detCore (scale t q) = t^2 * detCore q.

Therefore a nonzero normalisation scalar cannot manufacture a zero
determinant.

The central theorem is:

    BinarySchurBlock.pivot_of_scaled_detCore_eq_zero

and the packaged first-entry form is:

    FirstBinarySchurEntry.pivot_of_coefficient_detCore_eq_zero

Thus once the determinant-order calculation proves that the first nonzero
binary Schur coefficient has zero determinant, the rank-one pivot conclusion
is immediate.

No theorem statement from previous phases is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
