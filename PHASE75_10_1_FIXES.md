# Phase 75.10.1 — Defect exposure compile hardening

This patch changes no theorem statements or mathematical assumptions. It repairs the five elaboration/proof-shape failures reported after Phase 75.10:

1. Normalises the one-step aligned Smith legality inequality before converting it to a natural-number lower bound.
2. Replaces solver-dependent residual subtraction arithmetic with `Nat.add_sub_of_le`.
3. Relates `polynomialParameterOrder` to `smithFamilyCoefficientOrder` through the explicit `smithFamilyCoefficientParameterOrder` definition.
4. Proves positive residual coefficients have zero constant term using `Polynomial.coeff_X_pow_mul'` at coefficient zero.
5. Unfolds `canonicalSpecialFiberSmithPolynomial` before applying `coeff_smithSubfacePolynomial` in the packet-exposure theorem.

No `sorry`, `admit`, `unsafe`, or axioms are introduced.
