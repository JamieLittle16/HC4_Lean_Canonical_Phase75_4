# Phase 75.12 — Evaluated rigid-packet Hessian → zero-Schur clock

## Purpose

This phase closes the rigid Smith branch for ordinary degree `D ≥ 3` and
isolates the exact remaining degree boundary `D = 2`.

The key observation is that the Phase-75.10 defect-preserving Smith exposure
has a spatially constant Hessian determinant clock

    det Hess(P♯) = X^(20 * defect).

Therefore one may evaluate all spatial variables at a fixed scalar point
without changing the parameter determinant clock.

## New modules

### `HC4/Newton/RigidPacketEvaluatedHessianChart.lean`

For a rigid persistent packet

    x^(D-2) (A y^2 + B y z + C z^2)

and `3 ≤ D`, proves explicit scalar Hessian charts.

* Left pivot: evaluate at `(x,y,z,w) = (1,1,0,0)`, active pair `(x,y)`.
* Right-axis pivot: evaluate at `(1,0,1,0)`, active pair `(x,z)`.

In either chart the active determinant is nonzero in characteristic zero,
and the denominator-cleared complementary Schur block is zero.  In the
left chart the only nontrivial Schur formula is a multiple of the packet
discriminant; in the right chart the pivot conditions force the two other
quadratic coefficients to vanish.

### `HC4/Valuation/RigidPacketZeroSchurBridge.lean`

Adds spatial evaluation of a polynomial-parameter Hessian and proves:

1. the constant parameter coefficient is the Hessian of the special fibre
   evaluated at the same point;
2. simultaneous row/column permutation preserves the determinant;
3. exact Hessian defect `X^N` survives spatial evaluation;
4. the Phase-75.10 exposed rigid packet therefore builds an
   `ExactZeroSchurFourBlockData K` in either pivot chart;
5. Phase-75.11 then gives rank-two repair progress or exact closing data.

The final theorem is

    CanonicalSmithDepartureFrontier
      .rankTwoProgress_or_degreeTwo_or_rigidClosing

under the already-existing `2 ≤ D` hypothesis.  It returns exactly one of

* strict rank-one → rank-two repair progress;
* the remaining boundary `D = 2`;
* the two-stage determinant-closing Schur outcome.

No `3 ≤ D` assumption is silently inserted into the retained frontier.
The handwritten restart note states the stationary packet as `x^e q(y,z)`
with `e ≥ 1`; recovering that positivity from the Lean first-wall state
would remove the `D = 2` alternative immediately.

## Safety/static audit

The added files contain no `sorry`, `admit`, `unsafe`, or project `axiom`.
