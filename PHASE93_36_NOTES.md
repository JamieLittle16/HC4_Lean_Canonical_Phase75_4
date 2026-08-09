# Phase 93.36 — planar Keller fibres of the one-zero terminal face

Built against the clean Phase 93.35.2 tree.

## Constant transverse determinant

From the green one-zero factorisation

    -(S)^2 * Delta23 = 1

the transverse determinant `Delta23` is itself a unit in the ambient
multivariate polynomial ring.  Over a field, a unit multivariate
polynomial is a constant unit.  Thus

    Delta23 = C t

for a nonzero scalar `t`.

## Honest planar fibre

Reindex the ambient variables so that coordinates `2,3` are the left
summand `Fin 2` and coordinates `0,1` are the frozen right summand.

For a scalar c, specialise

    X0 = c
    X1 = 0

while keeping X2 and X3 as honest planar variables.

The construction uses `MvPolynomial.aeval` after the reindexing.

## Differentiation commutes with fibre specialisation

Mathlib's

    MvPolynomial.aeval_sumElim_pderiv_inl

proves exactly that differentiation in a retained left-summand variable
commutes with specialisation of the right-summand variables.

Together with `MvPolynomial.pderiv_rename`, this yields

    d/du0 special(P) = special(pderiv 2 P)
    d/du1 special(P) = special(pderiv 3 P).

## Planar Keller certificate

Let H_c be the specialised potential.  Its planar gradient map has
Jacobian determinant

    special_c(Delta23).

Since `Delta23 = C t`, the planar Jacobian is exactly `C t` with `t != 0`.

The phase therefore proves

    standardOneZeroFibreGradientMap_hasKeller

and, under the existing `PlanarJC2Injectivity K` interface,

    standardOneZeroFibreGradientMap_injective_of_JC2.

This isolates the only remaining work for the standard k=1 endpoint:
relate ambient gradient values at arbitrary points to the common
X1=0 planar fibre after Phase 93.35 has already recovered X0, then recover
X1 from the gradient's coordinate 0.

No theorem statement from previous phases is weakened.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
