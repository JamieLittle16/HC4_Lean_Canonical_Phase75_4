# Phase 75.4.3 — Actual parameter-layer coefficient proof fix

This micro-patch replaces the brittle `simp` proof of
`familyParameterLayer_coeff` with an explicit calculation:

1. expand `MvPolynomial.sum` using `MvPolynomial.sum_def`;
2. push `coeff` through the finite sum with `MvPolynomial.coeff_sum`;
3. evaluate monomial coefficients using `MvPolynomial.coeff_monomial`;
4. collapse the single surviving term with `Finset.sum_ite_eq'`;
5. discharge the off-support case with `MvPolynomial.notMem_support_iff`.

No definitions or theorem statements are changed.
