# Phase 90.3.1 fix

Affected file:

    HC4/Newton/FirstSchurDeterminantOrder.lean

`firstFactor` is a namespace function depending only on the order `e`; it is
not a field of `BinarySchurTail`. Phase 90.3 accidentally wrote

    T.firstFactor e

in two places. Lean therefore inserted an error placeholder into the
determinant identity, which also caused the subsequent `ring` failure.

Phase 90.3.1 replaces both occurrences by

    firstFactor e

with no mathematical or theorem-statement change.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
