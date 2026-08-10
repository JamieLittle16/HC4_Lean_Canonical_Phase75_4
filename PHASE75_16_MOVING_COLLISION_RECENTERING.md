# Phase 75.16 — moving-collision recentering

This phase formalises the affine step that must precede the terminal
source-lattice associated graded.

New modules:

- `HC4/Valuation/MovingCollisionRecentering.lean`
- `HC4/Valuation/RigidClosingRecenteredSource.lean`

The key construction is

    Q_tau(Y) = P^sharp_tau(Y + a^sharp(tau)).

It proves exact evaluation, gradient, Hessian and determinant covariance,
then packages the rigid-closing source with identically-zero left section
and right special point `e0`.

This is deliberately not claimed to preserve ordinary source homogeneity:
translation is the mechanism by which lower Taylor degrees, especially the
terminal quadratic part, can appear.  The next theorem must prove weighted
homogeneity of the source-lattice initial form, not ordinary homogeneity of
this recentered family.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
