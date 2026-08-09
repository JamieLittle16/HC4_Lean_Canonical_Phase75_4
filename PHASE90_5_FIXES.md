# Phase 90.5 — polynomial/Rees rank-two Schur first entry

## New module

    HC4/Newton/RankTwoReesSchurEntry.lean

This phase completes the algebraic enclosure of the rank-two first-entry
branch.

It introduces a polynomial-valued adapted 4x4 block and proves the same
cleared Schur determinant identity as Phase 90.4 over `Polynomial K`.

A `RankTwoReesSchurEntry` then records an explicit common first Schur order:

    U = X^e A
    V = X^e B
    W = X^e C

together with nonvanishing of the evaluated tail block
`(A(0),B(0),C(0))`.

The theorem

    tail_scaledDeterminant_eq_schurDeterminant

identifies the polynomial 4x4 Schur determinant with the
`BinarySchurTail.scaledDeterminant` from Phase 90.3.

Finally,

    firstEntryPivot_of_determinantCore_eq_zero

proves that determinant-zero of the adapted polynomial 4x4 block forces the
first nonzero binary Schur coefficient to carry the Phase 90.1 pivot
certificate.

Thus, once the geometric/Hessian layer supplies an adapted rank-two Rees
block and its first common Schur order, the rank-one pivot conclusion is
fully automatic.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
