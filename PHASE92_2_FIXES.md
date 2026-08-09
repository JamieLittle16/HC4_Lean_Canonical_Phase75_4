# Phase 92.2 — persistent-packet binary quadratic classification

## New module

    HC4/Newton/RankOnePacketQuadratic.lean

Phase 92.1 exposes the three coefficients `A,B,C` of the first persistent
rank-one packet

    x^(D-2) * (A y^2 + B y z + C z^2).

This phase packages them as the denominator-cleared symmetric block

        [ 4A  2B ]
        [ 2B  4C ].

This is four times the usual symmetric matrix with off-diagonal `B/2`.
The denominator-free normalisation deliberately avoids any fragile division
API.

Lean proves:

* the block quadratic is exactly four times the original binary quadratic;
* `detCore(block) = -4 * (B^2 - 4AC)`;
* a nonzero packet gives a nonzero block in characteristic zero;
* `detCore = 0` iff the conventional discriminant is zero;
* discriminant zero inherits the explicit Phase 91 square/pivot geometry;
* every nonzero packet therefore splits into:
    - discriminant zero / rank-one square geometry, or
    - discriminant nonzero / nondegenerate rank-two transverse block.

This is the first formal re-entry interface from the rank-one persistent
packet into the already-checked binary Schur machinery.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
