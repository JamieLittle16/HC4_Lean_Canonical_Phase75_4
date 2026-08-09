# Phase 93.56 — Kernel inflation and Hessian defect

Built over the green Phase 93.55.1 tree.

This phase closes the missing determinant-factor calculation for the
concrete integral kernel blow-up.

## Ring-hom inflation

`kernelInflateHom` is the actual polynomial substitution

    T -> tau^q T

with all other source variables and coefficient polynomials fixed.

`kernelInflate_integralKernelBlowupFamily_eq` proves that applying this
substitution to the explicit quotient polynomial constructed in Phase 93.52
recovers the original family exactly.

## Chain rule

`pderiv_kernelInflateHom` proves the first-order formal chain rule by
`MvPolynomial.induction_on`.

`hessian_kernelInflateHom_entry` applies it twice.

## Determinant factor

`hessianDeterminant_kernelInflateHom` proves

    det Hess(Inflate_q Q)
      =
    C(tau^q)^2 * Inflate_q(det Hess Q).

`hessianDeterminant_integralKernelBlowup_factor` specialises this to the
actual Phase 93.52 integral blow-up:

    det Hess(P)
      =
    C(tau^q)^2 * Inflate_q(det Hess(Ptilde)).

This is the exact algebraic identity needed to extract

    Delta(Ptilde) = Delta(P) - 2q.

## Remaining step

The next phase should cancel the nonzero factor and use injectivity of the
diagonal inflation map to turn this factored identity into the literal
target defect theorem, then construct `HasPositiveKernelDefectDrop`
rather than receiving it as an input in Phase 93.55.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
