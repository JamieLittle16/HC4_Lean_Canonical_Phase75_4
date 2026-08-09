# Phase 93.34 — standard one-zero terminal factorisation

Built against the clean Phase 93.33.3 tree.

The strictly-positive k=0 terminal collision branch is now green and closed.
This phase attacks the remaining k=1 boundary in standard coordinates.

## Standard weight

Introduces

    standardOneZeroTerminalWeight d a = (0,d,a,d-a)

under

    0 < a < d.

The three nonzero weights are strictly positive and coordinate zero is the
unique zero-weight coordinate.

## Weight-zero derivative

For a potential F of weighted degree d, `pderiv 1 F` has weighted degree
zero.  Since coordinates 1,2,3 have positive weights, every supported
monomial of `pderiv 1 F` has zero exponent in those coordinates.

Therefore `pderiv 1 F` depends only on X0 and

    pderiv 1 (pderiv 1 F) = 0
    pderiv 2 (pderiv 1 F) = 0
    pderiv 3 (pderiv 1 F) = 0.

## Sparse determinant

A generic matrix

    [ a p b c ]
    [ q 0 0 0 ]
    [ r 0 e f ]
    [ s 0 g h ]

has determinant

    -p*q*(e*h-f*g).

For the actual Hessian, mixed-partial symmetry makes p=q=S where

    S = pderiv 0 (pderiv 1 F).

Hence

    hessianDeterminant F
      =
    - S^2 * Delta23,

where Delta23 is the Hessian determinant in the two interior positive
coordinates.

## Monge--Ampere consequence

Under `IsPolynomialMongeAmpere F`,

    - S^2 * Delta23 = 1.

The phase records:

* `S != 0`;
* `Delta23 != 0`;
* the explicit inverse relation

      S * (-S * Delta23) = 1.

This is the exact algebraic lever needed to show the zero/degree direction
is affine/invertible.  The next phase can convert the explicit polynomial
inverse into constancy of S, recover X0 from the gradient's X1-component,
then solve the positive 2,3 block recursively and finally recover X1.

No general torus theorem is used.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
