# Phase 75.4.1 — ActualParameterLayer compile fix

This is a minimal corrective patch for Phase 75.4.

It fixes the argument order used for `Polynomial.coeff` in
`HC4/Valuation/ActualParameterLayer.lean`.

In the pinned mathlib/Lean environment, the coefficient polynomial is the
first argument (`c.coeff j`), not the exponent.  The original Phase 75.4
spelling made Lean infer `j` as a polynomial and caused the downstream
membership theorem and `rcases` failures.

No theorem statement or mathematical definition is weakened or changed.
