# Phase 86.1 fixes

Phase 86 failed in `LogarithmicSourceRatFunc.lean` while trying to prove that
the canonical denominator of the reduced `eta` rational function divides the
manifest denominator `D^2`.

The direct call to `RatFunc.denom_div_dvd` was correct mathematically but
`simpa` over-unfolded the proposition in the pinned Mathlib build and reduced
the source theorem to `True` before it could match the desired target.

Phase 86.1 reuses the already kernel-checked Phase 84.1 wrapper
`canonicalReduced_denominator_dvd` instead.  The underlying statement and all
mathematics are unchanged.
