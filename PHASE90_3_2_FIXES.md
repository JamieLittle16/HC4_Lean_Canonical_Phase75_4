# Phase 90.3.2 fix

Affected file:

    HC4/Newton/FirstSchurDeterminantOrder.lean

Lean 4.24 could not infer the coefficient field in the call

    pow_ne_zero 2 (firstFactor_ne_zero e)

because `firstFactor e` carries the field only as an implicit parameter.

Phase 90.3.2 pins the type explicitly:

    ((firstFactor e : Polynomial K) ^ 2) ≠ 0

and calls

    firstFactor_ne_zero (K := K) e

No mathematical or theorem-statement change is made.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
