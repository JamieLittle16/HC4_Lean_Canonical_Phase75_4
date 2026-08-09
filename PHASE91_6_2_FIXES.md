# Phase 91.6.2 — deterministic solved recurrence proof

Affected file:

    HC4/Newton/DirectionalCoefficientRecurrence.lean

Phase 91.6.1 cleared the denominator correctly, but then asked `nlinarith`
to reason through products in an arbitrary field.  That automation does not
reliably treat the resulting field expression as the intended algebraic
rearrangement.

Phase 91.6.2 removes the tactic gamble.

From the already-proved recurrence

    den * coeff_i + num * coeff_j = 0

the proof first derives explicitly

    den * coeff_i = -(num * coeff_j)

using `linear_combination`.

It then applies `eq_div_iff` only to the genuine single quotient

    coeff_i = (-(num * coeff_j)) / den

and finally rewrites that expression, by commutative-ring normalization, to

    coeff_i = (-num / den) * coeff_j.

The theorem statement and mathematics are unchanged.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
