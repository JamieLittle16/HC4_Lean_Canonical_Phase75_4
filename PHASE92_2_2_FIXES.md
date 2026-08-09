# Phase 92.2.2 — BinarySchurBlock namespace qualification

Affected file:

    HC4/Newton/RankOnePacketQuadratic.lean

The Phase 91.1 theorem `squareGeometry_of_detCore_eq_zero` is declared
inside the namespace

    HC4.Newton.BinarySchurBlock

so it is not available as an unqualified top-level identifier in the
Phase 92.2 module.

Phase 92.2.2 changes the single call to

    BinarySchurBlock.squareGeometry_of_detCore_eq_zero

The theorem's exact namespace and signature were checked against the
green Phase 91.1 source.

No theorem statement or mathematical content is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
