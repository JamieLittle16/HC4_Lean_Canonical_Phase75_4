# Phase 92.2.1 — ordinary theorem application repair

Affected file:

    HC4/Newton/RankOnePacketQuadratic.lean

Lean 4.24 rejected two theorem invocations written using field notation
split across a line break:

    (rankOnePacketQuadraticBlock ...).
      squareGeometry_of_detCore_eq_zero

and

    (rankOnePacketQuadraticBlock ...).
      pivot_of_detCore_eq_zero

The underlying theorems and arguments are correct.  Phase 92.2.1 rewrites
both calls as ordinary theorem applications:

    squareGeometry_of_detCore_eq_zero (rankOnePacketQuadraticBlock ...) ...

and

    BinarySchurBlock.pivot_of_detCore_eq_zero
      (rankOnePacketQuadraticBlock ...) ...

No theorem statement or mathematical content is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
