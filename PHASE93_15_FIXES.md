# Phase 93.15 — symmetric Smith balance refinement

## New module

    HC4/Newton/SmithSymmetricBalanceRefinement.lean

The green Phase 93.14 pointwise classification allows varying
negative-first parameters `k` and negative-second parameters `l`.

Rather than introduce finite minima, this phase observes that the single
Phase 93.6 separator with `k=l=1` already solves the finite balance problem.

That separator is

    theta = (2,2).

On every general surviving grade its derivative is nonnegative:

    (-1,k)  ->  2(k-1) >= 0
    (l,-1)  ->  2(l-1) >= 0
    (0,0)   ->  0
    (a,b) in N^2 \ {0} -> strictly positive.

Therefore its zero set among surviving grades is exactly

    (-1,1), (0,0), (1,-1).

The new finite subface

    smithSymmetricBalancedSubface

keeps precisely the old minimum-face terms with zero symmetric derivative.

Using the green Phase 93.9 pole-minimality witness theorem, Lean proves
this refined subface is nonempty.

It then proves every exponent on the refined subface has one of the three
target grades.  After excluding the w-linear zero-grade blocker, those
grades are exactly the exponent patterns

    (b,c,d) = (0,2,0), (1,1,0), (2,0,0),

i.e. `z^2`, `yz`, `y^2`.

The main theorem is

    poleMinimal_symmetricSmithRefinement_quadratic.

This is stronger and cleaner than the fixed-(k,l) Phase 93.10 interface:
no common extreme parameter and no finite-minimum construction is needed.

The next bridge is to attach the longitudinal exponent and identify this
refined quadratic subface with the existing
`HasRankOnePersistentPacketSupport` model used by Phase 92/93.4.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
