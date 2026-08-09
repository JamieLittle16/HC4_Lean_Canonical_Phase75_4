# Phase 88.8 fixes

Affected file:

    HC4/RationalRigidity/RankThreeInfinityAssembly.lean

Phase 88.7 exposed two pinned-API mismatches:

1. `RatFunc.algebraMap_ne_zero` concerns the polynomial embedding
   `K[X] -> RatFunc K`, not the scalar embedding `K -> RatFunc K`.
2. The goal contains `algebraMap ... (b⁻¹)`, not
   `(algebraMap ... b)⁻¹`.

Phase 88.8 avoids both conversions.

After normalising `Polynomial.aeval_C`, it uses commutativity to place

    algebraMap K (RatFunc K) b⁻¹

next to

    algebraMap K (RatFunc K) b.

The pair is folded back to

    algebraMap K (RatFunc K) (b⁻¹ * b)

using the ordinary ring-hom `map_mul` law. The field identity
`b⁻¹ * b = 1` then follows directly from `hb : b ≠ 0`, and `simp` closes
the goal.

No theorem statement changes. No `sorry`, `admit`, `unsafe`, or new axiom.
