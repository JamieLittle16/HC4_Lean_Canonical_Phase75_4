# Phase 75.12.6 — Explicit optionEquivLeft arguments

Fixes the pinned-mathlib application of `MvPolynomial.optionEquivLeft_X_none` in
`HC4/Valuation/SmithFrontierFourBlockExtraction.lean`.

In this mathlib revision the ring and variable types are explicit parameters, so the theorem is
applied as:

```lean
MvPolynomial.optionEquivLeft_X_none K (Fin 4)
```

No theorem statements or mathematical assumptions change.
