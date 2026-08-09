# Phase 88.5 fixes

Affected file:

    HC4/RationalRigidity/RankThreeInfinityAssembly.lean

The Phase 88.4 build reached a single remaining goal in
`rankThree_polynomial_autonomous_equation_of_constant_denominator`:

    RatFunc.C b * (RatFunc.C b)⁻¹ * logarithmicSourceEtaRatFunc phi
      = logarithmicSourceEtaRatFunc phi

with hypothesis `hb : b ≠ 0`.

Phase 88.5 transports `hb` through the canonical constant embedding by using
the pinned Mathlib theorems `RatFunc.algebraMap_C` and
`RatFunc.algebraMap_ne_zero`, obtaining `RatFunc.C b ≠ 0`. `simp` can then
perform the field cancellation directly.

The ineffective `ring` fallback is removed.

No theorem statement is changed. No `sorry`, `admit`, `unsafe`, or new axiom
is introduced.
