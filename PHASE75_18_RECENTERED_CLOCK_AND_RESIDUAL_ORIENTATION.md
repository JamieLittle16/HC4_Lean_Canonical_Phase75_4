# Phase 75.18 — Recentered Schur clock and residual orientation

This phase repairs a subtle provenance mismatch in the rigid-closing endgame
and proves the first source-level orientation theorem for the positive residual
branch.

## 1. Recentered special fibre

`MovingCollisionRecentering.lean` now proves that translating a polynomial
family by a moving section whose special point is zero leaves the parameter
special fibre unchanged.

Therefore the rigid packet carried by the defect-preserving Smith exposure is
still the special fibre after recentering at the left moving collision section.

## 2. Refresh the Schur clock after recentering

`RigidClosingRecenteredSchurClock.lean` rebuilds the left/right rigid evaluated
four-blocks on the recentered family itself.  The exact Hessian determinant
clock is unchanged by translation, and the constant Schur block is still the
same rigid zero-Schur packet chart.

The green two-stage zero-Schur theorem is then rerun.  Hence recentering gives
one of:

* immediate rank-one -> rank-two repair progress; or
* a provenance-preserving closing clock attached to the recentered family.

No theorem identifies the old pre-translation clock with the new one.

## 3. Feed the refreshed clock into Phase 75.17

`RigidClosingFirstKernelStage.lean` gains a block-parametric closing split.
`RigidClosingRecenteredFirstKernelAssembly.lean` uses it to rerun the existing
finite-support/global-kernel dichotomy with the refreshed block.

Thus the first Schur order and coefficientwise source integrality now refer to
the same polynomial family.

## 4. Residual orientation

`RigidClosingResidualOrientation.lean` proves the source-level factor law for
the common first kernel coordinate `3`.

If

    Q = Inflate_3,e(Qtilde),

then at either rigid chart point the cleared Schur kernel entry satisfies

    schurC(Q) = X^(2e) * schurC(Qtilde).

The rigid chart points both have coordinate 3 equal to zero, so spatial
evaluation commutes with this reinflation without moving the evaluation point.

Consequently, after the zero-Schur clock removes only its common factor X^e,
the normalised tail has

    tail.kernel.coeff 0 = 0.

When the residual determinant order is positive, the tail determinant-zero
identity forces the constant off-diagonal coefficient to vanish.  Since the
constant tail block is nonzero, its active coefficient is nonzero.  Hence the
residual tail is a left pivot.

This removes the arbitrary residual-pivot ambiguity after a successful first
global stage.  The remaining second source kernel is therefore the other
residual source direction (coordinate 2 in the left chart, coordinate 1 in the
right chart).

## Audit

No theorem in this patch assumes that the old pre-recentering Schur clock is
preserved by affine translation.  No `sorry`, `admit`, `unsafe`, or new
`axiom` declarations are intentionally present.
