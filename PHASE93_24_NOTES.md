# Phase 93.24 — actual terminal Hessian at the origin

## New module

    HC4/Newton/TerminalActualHessian.lean

Phase 93.23.1 is green.

Rather than require a separate entry-by-entry identification between the
restart Hessian and the coefficient Hessian, this phase proves the exact
fact needed by the scalar terminal argument directly.

It defines the actual evaluated Hessian entry

    eval_point (pderiv i (pderiv j F))

and expands it over the finite support of `F`.

Using only the pinned and already-used theorem

    MvPolynomial.pderiv_monomial

plus evaluation at zero, Lean proves:

    nonzero monomial contribution to Hess_{ij}(F)(0)
        ->
    exponent = X_i X_j.

Therefore

    Hess_{ij}(F)(0) != 0
        ->
    [X_i X_j]F != 0.

A nonzero determinant of the four-coordinate actual Hessian supplies a
nonzero matrix entry, hence a genuine quadratic coefficient witness.

The main theorem

    scalarTerminal_actualHessian_nondegenerate_endpoint

then combines this witness with the green Phase 93.22 scalar-weight theorem
to return

    F != 0  AND  HasPureQuadraticSupport F

directly from the actual terminal Hessian determinant.

This is stronger for the restart application than introducing an extra
coefficient-matrix equality hypothesis.

Next target if green: package the non-scalar terminal weight as the
conformal-cocharacter endpoint, then assemble the exhaustive restart
classification.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
