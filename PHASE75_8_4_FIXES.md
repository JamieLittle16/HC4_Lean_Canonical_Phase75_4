# Phase 75.8.4 — Bridge projection and constant coefficient normalization

This patch is a surgical repair of the two remaining elaboration failures in
`HC4.Valuation.FirstSchurDepartureBridge` after Phase 75.8.3.

1. The closing branch now first proves the exact equality between the selected
   `firstPositiveTransverseOrder` and `f.defect`, then rewrites the nonzero
   transverse disjunction at that exact expression.
2. The left-pivot clearing-factor constant term is normalized through
   `Polynomial.C_pow`, so Lean sees the coefficient of the constant polynomial
   square as the scalar square already known to be nonzero.

No theorem statements or mathematical assumptions are changed.
