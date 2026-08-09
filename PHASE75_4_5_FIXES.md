# Phase 75.4.5 — pinned mapRange compatibility fix

This corrective micro-patch targets the exact mathlib revision pinned by the
Phase 75.2/75.4 project (`f897ebcf72cd16f89ab4577d0c826cd14afaafc7`).

It changes only `HC4/Valuation/ActualParameterLayer.lean`.

The unavailable newer APIs `AddMonoidAlgebra.map` and
`MvPolynomial.coeff_addMonoidAlgebraMap` are replaced by the APIs present in
the pinned revision:

- `Finsupp.mapRange`
- `MvPolynomial.coeff_mapRange`

No theorem statement or mathematical interface is changed.
