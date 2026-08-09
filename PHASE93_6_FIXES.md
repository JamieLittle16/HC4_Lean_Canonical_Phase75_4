# Phase 93.6 — two-extreme Smith balance and explicit separation

## New module

    HC4/Newton/SmithExtremeBalance.lean

This phase formalises the finite geometric core of the Smith convex-balance
step after the green Phase 93.5 lattice classification.

For the surviving negative-coordinate extremes

    p_k = (-1,k)
    q_l = (l,-1)

it defines a rational two-point convex balance and proves:

    SmithTwoExtremeBalance k l
      -> (k : Q) * (l : Q) = 1
      -> k*l = 1.

With `k,l >= 1`, Phase 93.5 then forces

    k = l = 1,

so the extremes are exactly

    (-1,1) and (1,-1).

The module also gives an explicit integral separator for the opposite case
`k*l > 1`:

    theta = (2k, k*l + 1).

Lean proves that this functional is strictly positive on both extreme
grades and on every nonzero first-quadrant grade.

This is the algebraic separation certificate needed for pole-minimality.
The next phase must connect such a separating Smith functional to a legal
infinitesimal valuation tilt.  That is the genuinely geometric half of the
convex-balance argument.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
