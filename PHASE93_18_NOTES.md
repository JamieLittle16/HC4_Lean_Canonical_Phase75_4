# Phase 93.18 — exact transverse collision → rigid rank-one packet

## New module

    HC4/Newton/RankOnePacketExactCollision.lean

Phase 93.17 leaves one local geometric input in coefficient form:
`HasPersistentQuadraticGradientZero`.

This phase replaces that interface with an actual exact polynomial-gradient
collision.

It defines the normalised transverse point

    x = 1, y = Y, z = Z,

and proves a persistent packet has an exact three-monomial normal form.
That normal form is rewritten into ordinary multivariate-polynomial syntax,
giving the evaluated derivative identities

    ∂_y F = 2 A Y + B Z
    ∂_z F = B Y + 2 C Z

at the normalised transverse point.

Therefore an exact gradient collision between the origin and that point
implies `HasPersistentQuadraticGradientZero`.  At a nonzero transverse
point, the green Phase 93.4 theorem then forces
`HasRigidRankOnePacket`.

The final theorem

    poleMinimal_symmetricSmithRestriction_rigid_of_exactCollision

applies the result to the canonical symmetric Smith restriction constructed
in Phase 93.17.

If green, the next global red box is no longer coefficient algebra:
prove that the actual first nonzero Rees/Smith restart wall induces the
required exact gradient collision on the canonical restricted polynomial.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
