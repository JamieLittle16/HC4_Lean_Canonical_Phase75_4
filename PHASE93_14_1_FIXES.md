# Phase 93.14.1 — explicit exponent arithmetic repair

Affected file:

    HC4/Newton/SmithFirstWallGradeClassification.lean

The Phase 93.14 failures came from asking `omega` to reason through
structure projections and opaque Smith-grade definitions at the same time.

The repaired proof destructures the exponent record immediately:

    e = ⟨b,c,d⟩.

The negative-coordinate branches then use the already-green shape lemmas
and explicitly substitute the forced zero exponents before any further
arithmetic.

This removes the nonexistent `Prod.fst_mk` / `Prod.snd_mk` constants and
lets the remaining grade equalities reduce to ordinary natural/integer
arithmetic.

For the nonnegative quadrant, the proof explicitly derives

    1 <= b+d
    1 <= c+d

before choosing the natural coordinates

    b+d-1, c+d-1.

The nonzero condition is proved by a direct case split rather than by
introducing binders into a disjunction goal.

No theorem statement or mathematical content is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
