# Phase 93.29 — exact planar Keller reduction of the two-zero endpoint

Built against the clean Phase 93.28.3 tree.

## TerminalTwoZeroPlanarisation

Turns the support-level statement "A and C depend only on variables 0,1"
into honest planar polynomials.

The standard inclusion `Fin 2 ↪ Fin 4` is used with Mathlib's
`MvPolynomial.exists_rename_eq_of_vars_subset_range`.

Thus there exist planar `A₂,C₂` such that

    rename A₂ = A,
    rename C₂ = C.

## TwoZeroBlockDeterminant

Kernel-checks the exact finite identity

    det [ B  Jᵀ ]
        [ J   0 ] = (det J)^2

for the concrete 4x4 / 2x2 block shape needed here.

The proof uses `Matrix.det_succ_row_zero`,
`Matrix.det_fin_three`, and `ring`, matching the already-green rank-three
determinant style elsewhere in HC4.

## TerminalTwoZeroHessianSquare

Identifies the actual polynomial Hessian of the standard two-zero terminal
potential with that block matrix, using the green positive-positive Hessian
vanishing and the project-local `pderiv_comm_backport`.

This yields the polynomial identity

    hessianDeterminant F
      = (A₀*C₁ - A₁*C₀)^2.

## TerminalTwoZeroKellerReduction

Now explicitly carries the global terminal Monge--Ampère hypothesis

    IsPolynomialMongeAmpere F
    i.e. det Hess(F) = 1.

The planar Jacobian determinant renames to the ambient cross determinant.
Since the variable renaming is injective,

    Jac(A₂,C₂)^2 = 1

in `MvPolynomial (Fin 2) K`.

Because this polynomial ring over a field is a domain,

    Jac(A₂,C₂) = 1  or  Jac(A₂,C₂) = -1.

Hence the descended pair is a genuine
`HasNonzeroConstantPlanarJacobian` map.

The final theorem feeds this certificate to `PlanarJC2Injectivity` and
returns an injective planar base map.

What remains for the k=2 branch after this phase is the exact conjugacy
between the four-variable gradient and the already-green abstract
`doublingGradientMap`.  Once that is formalised, a distinct terminal
collision gives an immediate contradiction under JC2.

No general torus theorem is used.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
