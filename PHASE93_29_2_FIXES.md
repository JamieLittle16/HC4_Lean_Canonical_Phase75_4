# Phase 93.29.2 — final Keller branch local-let simplification

Affected module:

    HC4/Newton/TerminalTwoZeroKellerReduction.lean

The Phase 93.29.1 build reached the final two branches proving that the
planar Jacobian determinant is the constant `1` or `-1`.

Both failures were caused by

    dsimp [G] at hJ

reporting that it made no progress.

At that point the useful equality is already

    hJ : J = 1

or

    hJ : J = -1,

with local definitions

    J := planarJacobianDetPolynomial G
    G := standardPlanarPairMap A C.

The repair removes the standalone `dsimp` and closes each branch directly
with

    simpa [J, G] using hJ.

This unfolds both local definitions only where needed.

No theorem statement or mathematical hypothesis changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
