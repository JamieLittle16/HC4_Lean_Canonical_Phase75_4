# Phase 91.6.1 — solved recurrence denominator repair

Affected file:

    HC4/Newton/DirectionalCoefficientRecurrence.lean

The underlying adjacent-coefficient recurrence compiled; only the
presentation of the solved form failed.

Phase 91.6 attempted to use `eq_div_iff` directly on a target of the form

    coeff_i = (numerator / denominator) * coeff_j,

whereas `eq_div_iff` expects a single quotient on the right.  The theorem
statement is unchanged.

Phase 91.6.1 instead:

1. proves the same denominator is nonzero;
2. clears it with `field_simp [hden]`;
3. closes the resulting polynomial equality from the already-proved
   recurrence using `nlinarith`.

No mathematical statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
