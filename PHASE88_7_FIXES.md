# Phase 88.7 fixes

Affected file:

    HC4/RationalRigidity/RankThreeInfinityAssembly.lean

Phase 88.6 attempted to commute a `RatFunc.C b` factor, but after rewriting
`hB` Lean still represented the constant denominator as

    Polynomial.aeval (...) (Polynomial.C b)

and represented the inverse scalar through

    algebraMap K (RatFunc K) b.

Phase 88.7 therefore normalises `Polynomial.aeval_C` first and stays entirely
in the scalar `algebraMap` representation shown by Lean.

It proves

    algebraMap K (RatFunc K) b ≠ 0

directly from `hb` with `RatFunc.algebraMap_ne_zero`, uses `ac_rfl` only for
associative/commutative rearrangement, and then lets `simp` cancel the adjacent
inverse/product pair.

No theorem statement is changed. No `sorry`, `admit`, `unsafe`, or new axiom
is introduced.
