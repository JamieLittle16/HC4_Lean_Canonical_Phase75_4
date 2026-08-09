# Phase 93.71 — Coupled Smith wall closure

Built over the green Phase 93.70.1 tree.

## Core theorem

The coupled first wall is impossible in the nonprimitive branch.

At a coupled wall:
- the marked section wall forces the common first step `N` to be positive;
- every coefficient that survives on the transformed special fibre has
  exact aligned residual order zero;
- without an original order-zero zero-grade source coefficient, residual
  zero at positive `N` forces strictly negative symmetric Smith derivative.

The only negative symmetric derivatives are `-4` and `-2`.

Ordinary degree-`D` homogeneity reconstructs their source monomials as
exactly:

    x^D,
    x^(D-1) y,
    x^(D-1) z.

Hence the entire first-wall special fibre is

    A x^D + B x^(D-1)y + C x^(D-1)z.

The Smith transformation leaves the longitudinal coordinates of the marked
special points equal to `0` and `1`.

Exact gradient collision then gives:
- y-component: `B = 0`;
- z-component: `C = 0`;
- x-component: `A = 0`.

So the special fibre is zero, contradicting the surviving coefficient wall.

## Headline

`alignedSmith_closedBoundaryDispatcher` removes the final coupled-wall
alternative.  Its output is exactly:

    canonical local repair/terminal
      OR
    strict fixed-scale defect restart.

Thus, conditional on this phase compiling cleanly, the local zero-slope
Smith endpoint analysis is closed.

The next phase should be final global assembly/audit, but the assembly must
still audit carefully how geometric transformed-family data are threaded
through the global restart recursion; the numerical `GlobalRestartState`
alone does not remember a family.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
