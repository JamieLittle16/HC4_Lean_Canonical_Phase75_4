# Phase 93.43 — Packaged Smith rank-one entrance

This is a larger closure patch over green Phase 93.42.

It removes another layer of auxiliary hypotheses from the local RS1 / Smith-first-wall spine:

1. `smithSymmetricBalancedSubface_subset` proves the canonical balanced subface is literally a subset of the ambient Smith support.
2. `smithSymmetricBalancedSubface_realisedInPolynomial` specializes this to the actual projected support and discharges the previous explicit refined-face realisation hypothesis.
3. `homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_nonzero_rankOnePacket` packages exact collision + pole minimality + attainment into a nonempty, nonzero canonical restriction with rank-one persistent packet support.
4. `HasNonzeroSmithFirstWallGradientCertificate` isolates the genuinely geometric residue: a nonzero transverse first-wall point with vanishing leading quadratic gradient.
5. `homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_rigid_of_firstWallCertificate` packages the complete local Smith balance/refinement/rank-one argument into one theorem returning `HasRigidRankOnePacket`.
6. `homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_rigid_of_nonzero_wall` is the explicit-coordinate variant for restart code that already exposes `Y,Z`.

Thus the canonical realisation and nonzero-packet obligations are no longer external inputs. After this patch, the remaining Smith/global interface is the restart extraction of the first-wall certificate itself (and later top-level restart assembly), rather than further finite Smith balance bookkeeping.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
