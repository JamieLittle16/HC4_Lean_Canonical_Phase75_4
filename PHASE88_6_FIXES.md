# Phase 88.6 fixes

Affected file:

    HC4/RationalRigidity/RankThreeInfinityAssembly.lean

Phase 88.5 correctly proved:

    hCb : RatFunc.C b ≠ 0

but the remaining goal had the factors ordered as

    (RatFunc.C b)⁻¹ * (eta * RatFunc.C b) = eta

so `simp [hCb]` could not see an adjacent inverse/product pair.

Phase 88.6 performs only the necessary commutative-ring normalization:

1. commute `eta` with `RatFunc.C b`;
2. reassociate the product;
3. simplify the adjacent `(RatFunc.C b)⁻¹ * RatFunc.C b` using `hCb`.

No theorem statement changes. No `sorry`, `admit`, `unsafe`, or new axiom.
