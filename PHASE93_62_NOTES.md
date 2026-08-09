# Phase 93.62 — Symmetric Smith minimality

Built over the green Phase 93.61.1 tree.

A source audit of the canonical Smith refinement reveals a major
simplification: the actual local classifier only uses the explicit
separator `(k,l) = (1,1)`.

Its direction is `(2,2)` and its denominator-clearing index is the fixed
integer `10`.

## New weak predicate

`IsSymmetricSmithPoleMinimal S m base` says only that the `(1,1)` separator
fails to strictly improve every supported rescaled value.

`HasStrictSymmetricSmithImprovement` is its exact complementary branch.

The theorem

    symmetricSmithPoleMinimal_or_strictImprovement

gives the one-separator dichotomy directly.

## Same local classifier

The phase reconstructs the symmetric balanced subface and proves it is
quadratic using only the weak predicate.

Then

    homogeneous_exactAxisCollision_symmetricMinimal_canonicalRepair

reuses:
- exact-axis low-pattern exclusion;
- canonical Smith subface construction;
- rank-one packet support;
- nonzero realisation;
- the existing rigid-or-rank-two repair theorem.

It returns the same `HasSmithCanonicalRepairOutcome` as the stronger
all-separators theorem.

The restart-facing wrapper

    smithFirstWall_hasRepairOrTerminal_symmetricMinimal

therefore supplies the same local terminal-or-repair interface.

## Fixed scale

Theorems record explicitly:

    smithExtremeSeparator 1 1 = (2,2)
    smithExtremeSeparatorBound 1 1 = 4
    smithSeparatorRamificationIndex 1 1 = 10.

This means the canonical Smith branch can be denominator-cleared by one
fixed ramification `tau -> s^10`, chosen once before the global restart.
The global defect can then be measured consistently on that single
ramified scale.

## Remaining positive-improvement adapter

The only Smith-global algebra still to connect is the complementary branch:

    HasStrictSymmetricSmithImprovement

on a once-ramified normalised family
    -> integral `(2,2)` Smith conformal transform
    -> one common parameter factor
    -> Phase 93.61 strict defect restart.

No quantification over arbitrary Smith separator denominators is needed.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
