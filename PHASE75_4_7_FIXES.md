# Phase 75.4.7 — pinned `MvPolynomial.coeff_C` repair

This patch changes only `HC4/Valuation/FirstSchurDepartureBridge.lean`.

The Phase 75.4.6 proof used `MvPolynomial.coeff_C_of_ne_zero`, which does not
exist in the project's pinned mathlib revision `f897ebcf72cd16f89ab4577d0c826cd14afaafc7`.

The pinned source provides instead:

```lean
@[simp]
theorem coeff_C [DecidableEq σ] (m) (a) :
    coeff m (C a : MvPolynomial σ R) = if 0 = m then a else 0
```

Therefore the nonzero-monomial branch is proved directly by rewriting with
`MvPolynomial.coeff_C` and simplifying with `hd : d ≠ 0`.

No theorem statements, definitions, or mathematical interfaces are changed.
