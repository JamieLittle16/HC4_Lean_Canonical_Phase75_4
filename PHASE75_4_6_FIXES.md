# Phase 75.4.6 — First Schur coefficient fix

Repairs the two remaining elaboration goals in
`HC4.Valuation.FirstSchurDepartureBridge`.

The proof of `hessianDefect_parameterLayer_eq_zero_of_lt` now explicitly:

1. uses `MvPolynomial.coeff_C` at the zero source monomial;
2. uses `Polynomial.coeff_X_pow` and `j ≠ Delta` to kill the pre-closing parameter coefficient;
3. uses `MvPolynomial.coeff_C_of_ne_zero` for every nonzero source monomial.

No theorem statements or mathematical interfaces are changed.
