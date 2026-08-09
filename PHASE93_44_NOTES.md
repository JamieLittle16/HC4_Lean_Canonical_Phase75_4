# Phase 93.44 — Certificate-free Smith re-entry

This patch is based on the exact Phase 93.43 first-wall checkpoint supplied by the user.

## Main change

The Smith first-wall spine no longer needs a nonzero transverse wall-gradient certificate merely to leave the unclassified rank-one regime.

After Phase 93.43, exact homogeneous axis collision + pole minimality + attainment already give a canonical nonzero persistent packet. The existing `rankOnePersistentPacket_reentry` theorem therefore applies immediately.

The new package proves:

1. construction of the nonempty/nonzero canonical Smith packet;
2. unconditional `HasRankOnePacketReentry`;
3. an expanded dichotomy:
   - determinant-zero square/axis geometry; or
   - nonzero transverse determinant + trivial kernel (genuine rank-two re-entry);
4. if the rank-two escape branch is unavailable, the result automatically collapses to square/axis geometry;
5. if the discriminant is nonzero, the full rank-two escape certificate is returned directly.

## New theorem entry points

- `homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_reentry`
- `homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_square_or_rankTwo`
- `homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_square_of_no_rankTwo`
- `homogeneous_exactAxisCollision_poleMinimal_symmetricSmithRestriction_rankTwo_of_discriminant_ne_zero`

## Why this matters

This gives a certificate-free alternative to forcing rank-one rigidity by first extracting a nonzero transverse collision. The remaining global task can instead route the nondegenerate branch into the existing rank-two repair machinery.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
