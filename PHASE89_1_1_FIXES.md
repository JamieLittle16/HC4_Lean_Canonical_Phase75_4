# Phase 89.1.1 fix

Affected file:

    HC4/Newton/LexicographicRefinement.lean

The final branch of `lexDominates_of_scaledWeight_le` proves that assuming
the primary weights are neither ordered in the desired direction nor equal
forces the reverse strict inequality. The scaled-weight domination
hypothesis then contradicts the strict scaled-weight inequality.

Phase 89.1 returned that contradiction directly while Lean still expected
a term of `lexDominates ...`.

Phase 89.1.1 explicitly invokes `exfalso` before closing the contradiction.

There is no mathematical change and no theorem statement change.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
