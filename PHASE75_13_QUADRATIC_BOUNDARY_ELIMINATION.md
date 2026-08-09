# Phase 75.13 — Quadratic Boundary Elimination

This phase removes the last degree boundary left by the green rigid-packet
zero-Schur bridge.

## Main idea

The canonical exact-collision entry carries homogeneity of the **whole**
polynomial family.  The compressed departure frontier previously retained
only special-fibre homogeneity.  Phase 75.13 retains full family homogeneity
through all three local Smith branches.

For a source-homogeneous quadratic family over an integral domain, the source
gradient is linear with constant Hessian matrix.  If the determinant of that
matrix is nonzero, `Matrix.exists_mulVec_eq_zero_iff` gives trivial kernel, so
an exact gradient collision forces the two source sections to coincide.

For the HC4 coefficient ring `Polynomial K`, exact Hessian defect gives

    det Hess = X^Delta != 0.

Hence a `D = 2` departure frontier is impossible: its two moving sections
would be equal, but their specialisations are the distinct canonical points
`0` and `e_0`.

## New reusable theorems

- `alignedSmithGenuineFirstWallFamily_isHomogeneous`
- `quadraticFamilyHessianMatrix`
- `homogeneous_two_gradient_eq_mulVec_domain`
- `homogeneous_two_exactGradientCollision_eq_domain`
- `quadraticPolynomialFamily_exactCollision_sections_eq`
- `CanonicalSmithDepartureFrontier.degree_two_impossible`
- `CanonicalSmithDepartureFrontier.rankTwoProgress_or_rigidClosing`

The final endpoint upgrades

    rank-two progress OR D = 2 OR closing

to

    rank-two progress OR closing

for every retained degree `D >= 2`.

## Files

- `HC4/Valuation/SmithFamilyHomogeneity.lean`
- `HC4/Valuation/QuadraticFamilyCollision.lean`
- `HC4/Valuation/DefectRetainingDepartureFrontier.lean`
- `HC4/Valuation/RigidPacketZeroSchurBridge.lean`

## Suggested build

```bash
lake build HC4.Valuation.SmithFamilyHomogeneity
lake build HC4.Valuation.QuadraticFamilyCollision
lake build HC4.Valuation.DefectRetainingDepartureFrontier
lake build HC4.Valuation.RigidPacketZeroSchurBridge
./verify.sh
```
