# Phase 93.67 — Finite aligned Smith first stop

Built over the green Phase 93.66.1 tree.

This is the large finite-selector step after the single ramification by 20.

## Finite wall sets

The patch constructs:
- negative source-coefficient walls;
- nonzero transverse section walls for both marked points;
- an explicit sentinel cap `5*Delta+1`.

The first stop is the minimum of the cap and all genuine walls.

It is proved to lie before every coefficient and section wall.

## Arithmetic legality

At the selected first stop:
- every aligned source-coefficient order is nonnegative;
- every nonzero transverse section order is nonnegative.

The proof uses the exact `-4/-2` coefficient-wall arithmetic from Phase
93.66 and the `y/z` and `w` section walls on the same lattice.

## Actual polynomial transformation

The patch then converts those arithmetic inequalities into the exact
Phase 93.59 predicates:
- `HasIntegralSmithConformalCoefficientDivisibility`;
- `HasIntegralSmithConformalSectionDivisibility` for both sections.

This constructs:
- `alignedSmithFirstStopFamily`;
- `alignedSmithFirstStopSectionLeft`;
- `alignedSmithFirstStopSectionRight`.

No formal Laurent object is introduced.

## Collision and Hessian transport

The selected family has exact pure defect

    20 * Delta

on the once-ramified scale, and the exact polynomial-family gradient
collision survives the whole transformation.

The headline package theorem is

    alignedSmithFirstStop_package.

It returns:
1. exact Hessian defect of the selected family;
2. exact collision of the selected marked sections;
3. endpoint split:
       firstStop = cap
   or  firstStop is a genuine coefficient/left-section/right-section wall.

## What remains

The transformation/selection algebra is now separated from endpoint
interpretation.

The next endpoint theorem must show:
- coefficient wall -> the selected special fibre has a nonpositive Smith
  grade and enters the green symmetric-minimal classifier;
- section wall -> the selected marked-point degeneration enters the
  one-zero/two-zero endpoint machinery;
- cap -> either a zero-grade special-fibre coefficient is present, or a
  common parameter factor / defect-budget argument forces strict progress.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
