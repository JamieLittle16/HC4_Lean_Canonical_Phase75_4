# Phase 93.9 — denominator clearing and pole-minimal Smith contradiction

## New module

    HC4/Newton/SmithPoleMinimality.lean

This phase formalises the "after clearing denominators" step in the restart
proof of pole-minimal convex balance.

For the Phase 93.7 tilt

    epsilon = 1 / (2(B+1))

define

    D = 2(B+1).

Lean proves the exact identity

    D * (base + epsilon*delta) = D*base + delta.

Thus strict improvement under the small rational tilt gives a strict
improvement for an integral rescaled weight.

The finite predicate

    IsPoleMinimalAgainstSmithSeparators

says that every explicit Phase 93.6 Smith separator, after this denominator
clearing, leaves at least one supported coefficient at or below the
rescaled old minimum.

The main theorem

    poleMinimal_no_positive_smithSeparator

shows that such a pole-minimal model cannot have an explicit Smith separator
strictly positive on every old minimum-face monomial.

The witness version

    poleMinimal_exists_nonpositive_face_grade

says that each explicit separator has a minimum-face monomial on which its
Smith derivative is nonpositive.

This closes the finite denominator-cleared contradiction.  A later global
adapter still has to prove that the actual pole-minimal pointed Laurent
model satisfies this finite predicate, i.e. that these denominator-cleared
Smith tilts are legal conformal cocharacters after the allowed
ramification.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
