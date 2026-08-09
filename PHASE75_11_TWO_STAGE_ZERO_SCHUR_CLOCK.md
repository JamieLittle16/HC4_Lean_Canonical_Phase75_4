# Phase 75.11 — Two-stage zero-Schur first-entry clock

## Why the clock changed

The Phase 75.10 defect-preserving exposure has special fibre equal to the
rigid Smith packet.  In the rigid branch that packet has the square/axis form
`x^(D-2) * L(y,z)^2`, hence depends on at most two linear forms and its
Hessian has rank at most two.  Therefore, after choosing a nonzero active
`2 x 2` Hessian minor, the denominator-cleared binary Schur complement has
**zero** constant block.  It is not legitimate to feed this directly into a
rank-one-constant Schur clock.

This phase formalises the correct two-stage clock.

## New module

`HC4/Newton/ZeroSchurFirstEntryClock.lean`

### Stage 1: zero Schur block

For a binary Schur series with all three constant entries zero, Lean:

1. selects the least positive order `e` at which any entry is nonzero;
2. proves all three entries are divisible by `X^e`;
3. constructs their normalised tails;
4. proves

       det S = X^(2*e) * det(tail).

For an exact determinant clock

       det S = Q * X^N,    Q.coeff 0 != 0,

it proves `2*e <= N` and cancels the common factor to obtain

       det(tail) = Q * X^(N - 2*e).

If `N - 2*e = 0`, the first coefficient block is nondegenerate exactly at
closure.  If `N - 2*e > 0`, the first coefficient block is nonzero and has
determinant zero, so over a domain it has a left or right rank-one pivot.

### Stage 2: residual rank-one clock

The determinant-zero first block is aligned by the already-green constant
congruence from `RankOneSchurSeriesAlignment`.  The residual tail is then an
`ExactRankOneSchurClockAt`, independent of any valuation frontier.  The green
first-transverse linearisation proves that a preterminal second departure has
nonzero off-diagonal coefficient and therefore gives the canonical strict
rank-one -> rank-two `RepairProgress` step.

Thus an exact zero-Schur four-block now has only the intended outcomes:

* strict rank-two repair progress;
* a nondegenerate first entry exactly at determinant closure;
* a rank-one residual Schur departure exactly at the remaining closing order.

## Four-block constructor

`ExactZeroSchurFourBlockData` packages only:

* the polynomial-valued symmetric `2+2` block;
* exact full determinant `X^N`;
* nonzero constant active minor;
* zero constant coefficients of the three cleared Schur entries.

From these fields the complete two-stage clock and its local dichotomy are
automatic.

## Scope

This patch is purely algebraic and introduces no new HC4 geometric
hypothesis.  The next valuation patch must prove that the Hessian of the
Phase 75.10 defect-preserving Smith exposure supplies the four fields above
(in the left or right rigid pivot chart).  The determinant field is already
available from Phase 75.10; the remaining work is the explicit rigid-packet
Hessian chart calculation.
