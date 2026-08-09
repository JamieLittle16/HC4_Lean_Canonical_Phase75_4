# Phase 75.10 — defect-preserving canonical Smith exposure

This phase resolves the two-clock issue between the original determinant-defect
parameter and the Smith separator filtration.

Instead of using the special-fibre Smith-Rees family by itself, it constructs
one honest parameter family by:

1. ramifying the original parameter by the canonical factor 20;
2. performing exactly one symmetric integral Smith step `(2,2)`;
3. dividing by the conformal multiplier `X^4` through the existing integral
   Smith machinery.

For a supported source coefficient with original parameter order `v` and
symmetric Smith separator `delta`, the aligned residual is `20*v + delta`.
At a canonical lossless frontier this is nonnegative: on `v=0` the special
fibre is symmetric-Smith minimal, while for `v>0` the only negative separator
values are `-4` and `-2`.

The principal endpoints are:

* `CanonicalSmithLosslessFrontier.oneStepSmith_integralCoefficients`;
* `CanonicalSmithLosslessFrontier.defectSmithExposureFamily`;
* `CanonicalSmithDepartureFrontier.defectSmithExposure_hessianDefect`;
* `CanonicalSmithLosslessFrontier.specialFiber_defectSmithExposure_eq_packet`;
* `CanonicalSmithDepartureFrontier.rankTwoProgress_or_rigidDefectExposure`;
* `CanonicalSmithDepartureFrontier.rigidPacket_pivot`.

Thus the transformed family retains the pure Hessian clock, now at defect
`20 * Delta`, while its special fibre is exactly the retained canonical Smith
packet.  The already-existing canonical outcome then either supplies rank-two
repair progress immediately or leaves a rigid packet with a concrete pivot
chart for the next Hessian/Schur adapter.

No `sorry`, `admit`, project `axiom`, or `unsafe` declaration is introduced.
