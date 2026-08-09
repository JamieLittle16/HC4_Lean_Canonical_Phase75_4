# Phase 91.1 — binary pivot geometry

## New module

    HC4/Newton/BinaryPivotGeometry.lean

Phase 90 finishes the rank-two Schur analysis with a nonzero
determinant-zero symmetric binary block. Phase 91.1 converts that algebraic
pivot certificate into explicit one-direction geometry.

For a left pivot (`a ≠ 0`, `a*c=b^2`), Lean proves:

    (-b,a)

is a nonzero kernel vector, and for

    Q(x,y) = a*x^2 + 2*b*x*y + c*y^2

the cleared square identity

    a * Q(x,y) = (a*x + b*y)^2.

For the right-axis pivot (`a=b=0`, `c ≠ 0`), Lean proves

    Q(x,y) = c*y^2.

The packaged theorem

    BinarySchurBlock.squareGeometry_of_detCore_eq_zero

therefore shows that every nonzero determinant-zero symmetric binary packet
is explicitly a one-direction square packet.

This is the geometric input needed before adding Hessian integrability and
homogeneity.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
