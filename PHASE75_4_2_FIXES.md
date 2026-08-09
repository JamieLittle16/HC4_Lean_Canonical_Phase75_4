# Phase 75.4.2 — exact parameter-layer coefficient fix

This micro-patch changes only `HC4/Valuation/ActualParameterLayer.lean`.

`familyParameterLayer_coeff` now unfolds the `MvPolynomial.sum` explicitly and
uses the already-established `MvPolynomial.coeff_sum` / `coeff_monomial`
pattern, split on membership of the source monomial in `P.support`.

No theorem statement, definition, or geometric assumption is changed.
