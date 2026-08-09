# Phase 93.19 — exact collision descends to the Rees special fibre

## New module

    HC4/Valuation/PolynomialFamilyCollisionSpecialFiber.lean

A finite Rees family is represented as

    P : MvPolynomial σ (Polynomial K),

with the univariate coefficient-ring variable serving as the Rees
parameter.

Moving marked sections are allowed:

    a b : σ -> Polynomial K.

The special fibre at parameter zero is

    MvPolynomial.map Polynomial.constantCoeff P,

and the marked sections reduce coordinatewise by `Polynomial.constantCoeff`.

The main generic theorem

    polynomialFamilyExactGradientCollision_specialFiber

proves that exact equality of source-gradient values over `K[τ]` descends
to exact equality of the special-fibre gradient at the reduced marked
points.

This is the formal coefficientwise statement used implicitly throughout
the pointed Laurent/restart argument.  Moving sections are handled
directly; they do not need to be constant in the Rees parameter.

The final adapter

    poleMinimal_symmetricSmithRestriction_rigid_of_familySpecialFiber

combines this generic specialisation theorem with the green Phase 93.18
Smith-packet collision theorem.

Its only new hypotheses say:

* an actual polynomial Rees family exists;
* its special fibre is the canonical symmetric Smith restriction;
* its exact-collision sections reduce to the origin and the nonzero
  normalised transverse point.

Everything after those identifications is now kernel-checked.

Next target: construct/identify the actual Smith/Rees family and prove these
three realisation statements from the restart data.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
