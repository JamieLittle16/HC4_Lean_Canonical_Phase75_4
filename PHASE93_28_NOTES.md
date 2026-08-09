# Phase 93.28 — exact two-zero terminal doubling support

Built against the clean Phase 93.27.2 tree.

This phase deliberately attacks the `k = 2` boundary of the nonnegative
conformal terminal theorem.  It does not assume or invoke a general torus
classification.

## TerminalTwoZeroPattern

After reordering two zero-weight coordinates to positions `0,1`, the
determinant matching permutation and `d > 0` force the other two weights to
be exactly `d`.  Hence

    lambda = (0,0,d,d).

## TerminalTwoZeroSupport

For the standard `(0,0,d,d)` weight, weighted homogeneity of degree `d`
with `d > 0` implies every supported monomial satisfies

    m 2 + m 3 = 1.

This is converted to Mathlib natural weighted homogeneity of degree one for
the auxiliary weight `(0,0,1,1)`.

Weighted Euler then gives the exact identity

    X 2 * pderiv 2 F + X 3 * pderiv 3 F = F.

Both derivatives `pderiv 2 F` and `pderiv 3 F` have weighted degree zero
for the auxiliary weight, hence depend only on variables `0,1`.

A support-to-derivative lemma then proves the complete positive-positive
Hessian block vanishes.

## TerminalTwoZeroDoublingForm

Names

    A = pderiv 2 F
    C = pderiv 3 F

and packages

    F = X 2 * A + X 3 * C,

with `A,C` supported only in variables `0,1`.

It also derives the first two gradient formulas by differentiating this
identity.

## TerminalTwoZeroEndpointInterface

Packages the exact ambient four-variable data that remains to be descended
to a true `MvPolynomial (Fin 2) K` planar map.

After this phase, the remaining `k = 2` endpoint work is:

1. planarise A and C;
2. prove the 4x4 Hessian determinant is the square of the planar Jacobian;
3. invoke `PlanarJC2Injectivity`;
4. apply the already-green abstract doubling injectivity theorem.

No proof escape hatch or new axiom is introduced.
