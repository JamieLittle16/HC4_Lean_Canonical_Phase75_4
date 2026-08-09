# Phase 93.23 — terminal quadratic Hessian nondegeneracy

## New module

    HC4/Newton/TerminalQuadraticHessian.lean

Phase 93.22.3 is green.

This phase formalises the nondegeneracy-to-quadratic-witness half of the
terminal conformal face.

Rather than depend on potentially version-sensitive repeated-pderivative
APIs, it defines the Hessian of the quadratic Taylor part directly from
coefficients:

    H_ii = 2 [X_i^2]F
    H_ij =   [X_i X_j]F.

On four selected terminal coordinates this gives a 4x4 matrix.

Lean proves:

* nonzero determinant implies some matrix entry is nonzero;
* a nonzero matrix entry implies the corresponding quadratic coefficient
  is nonzero;
* hence a nondegenerate terminal quadratic Hessian supplies exactly the
  quadratic witness required by Phase 93.22;
* under a scalar nonzero terminal weight and weighted homogeneity, the
  entire terminal fibre therefore has pure quadratic support;
* the same determinant certificate also proves the terminal polynomial is
  nonzero.

Main theorem:

    scalarTerminal_nondegenerate_endpoint

which returns

    F != 0  AND  HasPureQuadraticSupport F.

Next target: identify the determinant-closing Hessian furnished by the
actual terminal restart with `terminalQuadraticHessianMatrix`; then the
scalar terminal branch is sealed and the non-scalar branch can be packaged
as the conformal-cocharacter endpoint.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
