# Phase 90.1 — binary Schur pivot algebra

## New module

    HC4/Newton/BinarySchurPivot.lean

This begins the first-rank-entry formalisation.

Rather than importing general matrix rank or Smith normal form, Phase 90.1
isolates the exact two-dimensional algebra needed later. A symmetric block

    [ a  b ]
    [ b  c ]

with zero determinant satisfies `a*c = b*b`. If the block is nonzero, then:

- either `a ≠ 0`, giving a left rank-one pivot certificate;
- or `a = b = 0` and `c ≠ 0`, so the block is already a pure right-axis
  pivot.

The main theorem is:

    BinarySchurBlock.leftPivot_or_rightAxisPivot

and the derived theorem

    BinarySchurBlock.nonzeroDiagonal

records that a nonzero determinant-zero symmetric block has a nonzero
diagonal coefficient.

This is the algebraic core needed for the rank-two first Schur coefficient
in the later 4x4 Hessian entry theorem.

No existing theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
