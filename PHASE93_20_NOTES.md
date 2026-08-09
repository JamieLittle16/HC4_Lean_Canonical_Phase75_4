# Phase 93.20 — preterminal first-departure algebra

## New module

    HC4/Newton/PreterminalFirstDeparture.lean

The v5 audit identifies `FirstDepartureMatchesLocalModel` /
`MixedDepartureAdapter` as the remaining restart-exhaustion interface.

This phase formalises its universal algebraic core.

With leading Schur block

    [[b,0],[0,0]], b != 0,

the determinant coefficient linear in the first later kernel potential `P`
is represented by

    b * P_VV.

If that coefficient vanishes before determinant closure, Lean proves

    P_VV = 0.

It then proves the exact binary determinant identity

    det Hess_(U,V) P = -(P_UV)^2.

Hence the first departure has an exact dichotomy:

1. `P_UV != 0`:
   the binary determinant source is a nonzero negative square, furnishing
   the mixed-pivot certificate;

2. `P_UV = 0`:
   there is no binary mixed curvature, furnishing the affine/separated
   certificate.

Main theorem:

    preterminal_departure_dichotomy

and the stronger exact-source theorem:

    preterminal_mixedPivot_exact_source.

This deliberately does not invent a duplicate of the existing
`FiniteRepairTermination` state.  Once green, the next adapter should
package `IsPreterminalMixedPivotChannel` into the precise existing repair
hypotheses and package `IsPreterminalAffineSeparatedChannel` into the
existing affine/separated endpoint.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
