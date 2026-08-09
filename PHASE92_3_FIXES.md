# Phase 92.3 — rank-one persistent-packet re-entry certificate

## New module

    HC4/Newton/RankOnePacketReentry.lean

This phase turns the green Phase 92.2 discriminant dichotomy into the
algebraic re-entry statement needed for termination.

### Nonzero packet => nonzero quadratic

From

    HasRankOnePersistentPacketSupport x y z D F
    F != 0

Lean derives that at least one of the three canonical `YY`, `YZ`, `ZZ`
coefficients is nonzero.  No separate quadratic-nonzero hypothesis is
needed downstream.

### Nonzero determinant => genuine rank two

The new reusable predicate

    BinarySchurBlock.HasTrivialKernel

states that the two symmetric row equations have only the zero solution.
An explicit two-by-two elimination theorem proves

    detCore != 0 -> HasTrivialKernel.

Thus the nonzero-discriminant branch is genuinely two-dimensional in the
transverse variables.

### Re-entry theorem

    rankOnePersistentPacket_reentry

starts from a nonzero persistent packet and proves exactly one of the
following algebraic outcomes:

* discriminant zero, with the explicit Phase 91 square/axis geometry; or
* discriminant nonzero, determinant core nonzero, and trivial transverse
  kernel.

This closes the purely algebraic classification of the first persistent
rank-one packet.  The next theorem must connect the second outcome to the
next Rees/Schur rank entry and use it in a finite repair/termination
measure.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
