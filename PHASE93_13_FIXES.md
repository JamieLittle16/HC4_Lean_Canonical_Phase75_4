# Phase 93.13 — longitudinal Smith first-wall blocker

## New module

    HC4/Newton/SmithFirstWallLongitudinal.lean

Phase 93.12 (green) eliminates every transverse blocker

    x^(D-1) X_i,  i != x.

This phase treats the remaining pure longitudinal blocker `x^D`.

Lean proves

    homogeneous_longitudinal_contributor_eq_blocker.

Any homogeneous degree-D support monomial contributing nontrivially to the
x-gradient at the coordinate-axis point e_x is forced to have no support
away from x.  Homogeneity then forces its exponent to be exactly D.

Hence a supported `x^D` is the unique nonzero x-gradient contributor.
The green Phase 93.11 exact-collision theorem therefore excludes it:

    homogeneous_exactAxisCollision_no_longitudinalBlocker.

The final theorem

    homogeneous_exactAxisCollision_no_lowBlockers

packages the complete low-blocker exclusion:

* x^D is absent;
* x^(D-1) X_i is absent for every i != x.

For the Smith chart this includes

    x^D,
    x^(D-1)y,
    x^(D-1)z,
    x^(D-1)w.

Thus, once this phase is green, the low-wall collision obstruction is
closed at the homogeneous polynomial level.

The next target is to connect these support exclusions to the actual Smith
grade classification used by Phase 93.10.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
