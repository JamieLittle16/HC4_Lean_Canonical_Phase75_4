# Phase 91.4 — characteristic-zero Hessian-kernel rigidity

## New module

    HC4/Newton/CharZeroHessianKernelRigidity.lean

This phase closes the differential bridge left open by Phase 91.3.

The pinned Mathlib version predates `MvPolynomial.coeff_pderiv`, so the
module first proves a local backport of the coefficient identity

    coeff m (pderiv i F)
      = coeff (m + single i 1) F * (m i + 1).

That identity is then used to prove:

1. mixed formal partial derivatives commute;
2. in characteristic zero, `pderiv i F = 0` forces exponent zero in
   variable `i` for every nonzero monomial of `F`;
3. the two fixed Hessian-kernel row equations force `D F` to be
   support-theoretically independent of the two transverse variables.

Combining (3) with the positive transverse-degree support rigidity from
Phase 91.3 gives

    binaryDirectionalDeriv_eq_zero_of_hessianKernel_of_exactPositiveDegree

which is the formal statement

    Hessian kernel + positive transverse homogeneity => D F = 0.

A left-pivot specialization is also supplied for the canonical Phase 91.1
kernel direction `(-b,a)`.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
