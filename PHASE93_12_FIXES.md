# Phase 93.12 — transverse Smith first-wall blockers

## New module

    HC4/Newton/SmithFirstWallTransverse.lean

This is the first actual blocker-enumeration module rather than helper
infrastructure.

For a homogeneous degree-D polynomial at the coordinate-axis collision
point e_x, Lean proves:

    homogeneous_transverse_contributor_eq_blocker

For every transverse coordinate i != x, any support monomial whose
i-th derivative contributes nontrivially at e_x is forced to be exactly

    x^(D-1) X_i.

The proof is structural:

1. nonzero contribution forces the post-derivative exponent
       d - e_i
   to have no support away from x;
2. nonzero contribution forces d_i != 0;
3. the previous step plus i != x forces d_i = 1;
4. homogeneity then forces d_x = D-1.

The actual blocker, if supported, has nonzero contribution, so it is the
unique contributor to the i-th gradient component.

The final theorem

    homogeneous_exactAxisCollision_no_transverseBlocker

combines this uniqueness with the green Phase 93.11 exact-collision
contradiction and excludes every monomial

    x^(D-1) X_i,  i != x.

One generic theorem therefore covers the three Smith blockers usually
listed separately:

    x^(D-1)y,
    x^(D-1)z,
    x^(D-1)w.

In particular the w-linear zero-grade wall is excluded by the same
argument.

The remaining low blocker is the longitudinal pure-x monomial x^D, which
can be handled by the analogous x-gradient theorem next.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
