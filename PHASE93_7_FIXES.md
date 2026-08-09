# Phase 93.7 — finite-support valuation tilt

## New module

    HC4/Newton/FiniteValuationTilt.lean

This phase formalises the quantitative small-tilt argument behind
pole-minimal convex balance.

For a finite support with integral old valuations and integral tilt changes,
assume:

* every old value is at least the minimum `m`;
* every tilt change is bounded below by `-B`;
* every coefficient on the old minimum face has tilt change at least `1`.

Set

    epsilon = 1 / (2(B+1)).

Lean proves:

* `epsilon > 0`;
* `epsilon * B < 1`;
* an integral value at least `m` is either exactly `m` or at least `m+1`;
* every supported tilted value is strictly greater than the old minimum.

The final theorem is

    finiteSupportTilt_strictly_raises_minimum.

This is the exact finite-stability statement used in the handwritten
pole-minimal balance proof: face terms move upward, while no non-face term
can use the small tilt to cross the integral unit gap.

The next adapter must identify `delta` with the Smith dot product produced
by a conformal valuation tilt, and show the finite support admits a uniform
bound `B`.  Those are structural, rather than analytic, obligations.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
