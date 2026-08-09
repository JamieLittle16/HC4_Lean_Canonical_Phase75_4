# Phase 93.11 — generic exact-collision first-wall exclusion

## New module

    HC4/Newton/ExactCollisionFirstWall.lean

This phase factors the non-combinatorial part of `SmithFirstWall` into a
generic `MvPolynomial` theorem.

It defines the actual evaluated gradient component

    eval point (pderiv i F)

and the actual contribution of each support monomial to that component.

Lean proves:

    mvGradientComponentAt_eq_sum_support

so the gradient component is literally the finite sum of those support
contributions.

The predicate

    IsUniqueGradientContributorAt

therefore means:

* the target exponent belongs to the actual support;
* its actual derivative/evaluation contribution is nonzero;
* every other actual support exponent contributes zero.

For a homogeneous polynomial `F` of degree `D >= 2`, Lean uses Mathlib's
homogeneous partial-derivative theorem to prove

    homogeneous_gradient_zero_at_origin.

Hence an exact collision between the origin and any point `q` gives

    homogeneous_exactCollision_gradient_zero.

Combining this with uniqueness yields

    homogeneous_exactCollision_uniqueContributor_impossible

and its coordinate-axis specialization

    homogeneous_exactAxisCollision_uniqueContributor_impossible.

Thus the remaining hard Smith first-wall file no longer has to perform a
bespoke collision calculation.  It only needs to prove, via the existing
directional recurrence / wall ordering, that each forbidden low blocker is
the unique contributor to an appropriate gradient component at its first
wall.

No new geometric hypothesis is introduced.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
