# Phase 93.14 — corrected pointwise Smith first-wall grade classification

## New module

    HC4/Newton/SmithFirstWallGradeClassification.lean

The green Phase 93.12/93.13 collision theorems exclude the four low
Smith-wall blockers.

This phase isolates the pointwise arithmetic consequence at the exponent
triple `(b,c,d)`.

It defines the three low patterns relevant to negative Smith grades:

    (0,0,0)  -- pure longitudinal
    (0,1,0)  -- low negative-first
    (1,0,0)  -- low negative-second

and proves

    generalSurvivingSmithGradeShape_of_noNegativeLowPatterns.

Every surviving grade is therefore one of:

    (-1,k) with k >= 1;
    (l,-1) with l >= 1;
    (0,0);
    a nonzero first-quadrant integral grade.

Crucially, this does NOT assume that all negative-first terms share one
parameter k, or that all negative-second terms share one l.  That
assumption in the older Phase 93.10 interface was stronger than what the
low-blocker theorem alone supplies.

The finite-face wrapper

    HasGeneralSurvivingSmithFaceShape

is therefore the corrected interface for the next balance theorem.

The module also records that after excluding the w-linear pattern
`(0,0,1)`, zero Smith grade is exactly the `yz` exponent pattern.

Next: take finite minima among the positive negative-first/negative-second
parameters and rerun the explicit separator argument using those minima.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
