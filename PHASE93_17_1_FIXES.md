# Phase 93.17.1 — explicit `Finsupp.filter_apply` repair

Affected file:

    HC4/Newton/SmithRefinedFacePolynomial.lean

The only Phase 93.17 build failure was the coefficient formula for the
canonical Smith-subface restriction.

After unfolding, Lean's remaining goal was exactly the standard theorem

    Finsupp.filter_apply.

The repair replaces the unsuccessful `simp` invocation with that theorem
explicitly.

No theorem statement or mathematical content changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
