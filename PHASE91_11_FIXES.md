# Phase 91.11 — packet-level linear-power normal form

## New module

    HC4/Newton/LinearPowerPacketNormalForm.lean

Phase 91.10 proves the coefficient classification separately on every
frozen external slice. Phase 91.11 packages those slices into the full
coefficientwise packet normal form.

The predicate

    HasLinearPowerTransverseNormalForm u v i j n F

means:

1. every nonzero monomial of `F` has exact transverse degree `n`; and
2. there exists an amplitude function `a(r)`, depending only on a frozen
   external exponent vector `r`, such that

       coeff(r + k e_i + (n-k)e_j, F)
         = a(r) * choose(n,k) * v^k * (-u)^(n-k)

   for all `k ≤ n`.

This is precisely the coefficientwise content of

    F = a(X) * (v Y_i - u Y_j)^n.

The main theorem

    hasLinearPowerTransverseNormalForm_of_directionalDeriv_eq_zero

derives the packet normal form from exact transverse degree and
`D_(u,v) F = 0`.

The theorem

    hasLinearPowerTransverseNormalForm_of_hessianKernel

composes this with the Phase 91.4 characteristic-zero Hessian-kernel
rigidity theorem.

A left-pivot specialization is included for the generic `q.b ≠ 0`
orientation.  The complementary `q.b = 0` case is axis-normal and is
already covered by Phase 91.5.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
