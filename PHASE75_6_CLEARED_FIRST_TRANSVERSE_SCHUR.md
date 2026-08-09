# Phase 75.6 — cleared first-transverse Schur extraction

This phase sharpens the first-departure bridge in two ways.

1. It replaces the overly strong requirement that a Schur determinant layer
   equal the corresponding full Hessian determinant layer by the natural
   denominator-cleared identity

       det(Schur) = factor * fullDet.

   Since the exact Hessian defect kills every full determinant coefficient
   below closure, multiplication by an arbitrary cleared active factor cannot
   create a preterminal Schur coefficient.

2. It introduces `RankOneSchurSeries` and automatically selects the least
   positive order at which either the off-diagonal or kernel Schur entry is
   nonzero.  All lower transverse coefficients are then proved zero from
   minimality, so the Smith adapter no longer has to carry this bookkeeping.

The main endpoint is

    FrontierClearedRankOneSchurSeries
      .preterminal_canonicalStrictRepair_or_affineSeparated

which turns any genuine cleared rank-one Schur series whose first transverse
order lies below the determinant defect directly into the already-green
strict repair / affine-separated dichotomy.

No `sorry`, `admit`, or new axiom is introduced.
