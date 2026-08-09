# Phase 86.2 fixes

This is a minimal elaboration repair for `HC4/RationalRigidity/RankThreeReducedTarget.lean`.

It addresses the three errors exposed after Phase 86.1:

1. the two `Polynomial.aeval` identities stopped at commutatively equal `RatFunc` expressions; append `ring` after the existing simplification, exactly as in the already-green Phase 83 scalar evaluation lemmas;
2. the `FractionRing.algEquiv` transport did not unfold the rank-three scalar numerator/denominator, so `simpa` could not push the algebra equivalence through their ring operations; add those definitions to the simplifier.

No definitions, theorem statements, hypotheses, or mathematical arguments are changed.
