# Phase 91.2 — fixed-kernel Hessian integrability

## New module

    HC4/Newton/FixedKernelHessian.lean

This phase is the first layer using the actual `MvPolynomial.pderiv`
operators.

For a fixed transverse direction `(u,v)` in coordinates `i,j`, define

    D F = u * pderiv i F + v * pderiv j F.

`HasFixedBinaryHessianKernel` states that this direction annihilates both
rows of the binary Hessian:

    D (pderiv i F) = 0
    D (pderiv j F) = 0.

Lean proves

    D (D F) = 0.

The proof expands the directional derivative using the derivation laws and
then uses the two Hessian-row kernel equations.

The module also specializes the statement to the canonical Phase 91.1
left-pivot kernel `(-b,a)` and the pure right-axis kernel `(1,0)`.

This gives the formal differential rigidity needed before homogeneity is
used to turn `D²F = 0` into invariance along the kernel direction.

No existing theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
