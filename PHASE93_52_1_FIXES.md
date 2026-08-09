# Phase 93.52.1 — Import fix

Lean 4.24 / the pinned mathlib tree does not contain the module

    Mathlib.Algebra.MvPolynomial.Coeff

The coefficient APIs used by `IntegralKernelBlowup.lean` are already
available transitively through
`HC4.Valuation.PolynomialFamilyKernelRestart`.

This patch removes the nonexistent MvPolynomial coeff import and the
unnecessary explicit polynomial-coeff import.

No theorem statements or mathematical content are changed.
