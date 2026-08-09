# Phase 91.7 — finite directional recurrence uniqueness

## New module

    HC4/Newton/FiniteDirectionalRecurrence.lean

Phase 91.6 gives, on each frozen external coefficient slice, the recurrence

    u*(k+1)*c(k+1) + v*(n-k)*c(k) = 0.

Phase 91.7 proves that over a characteristic-zero field, when `u ≠ 0`, this
recurrence and the single endpoint coefficient `c 0` uniquely determine all
coefficients through degree `n`.

The main theorem is

    directionalRecurrence_unique

and the zero-endpoint corollary is

    directionalRecurrence_eq_zero_of_endpoint_zero.

The proof is finite induction.  At step `k+1`, characteristic zero makes
`u*(k+1)` nonzero; the two recurrence equations and the induction
hypothesis force equality of the next coefficients.

This deliberately separates recurrence uniqueness from the binomial
closed form.  The next phase only has to show that the coefficient sequence
of a chosen linear-form power satisfies this recurrence and has the same
endpoint value.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
