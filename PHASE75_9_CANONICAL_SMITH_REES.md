# Phase 75.9 — Canonical Smith-Rees special-fibre exposure

This phase corrects a filtration mismatch discovered during the frontier-to-Schur audit.

The parameter of `CanonicalSmithDepartureFrontier.lossless.family` is the DVR/collision
parameter controlling the Hessian defect. The persistent Smith packet is instead cut out
inside the special fibre by the symmetric Smith separator. The packet therefore must not be
identified with the constant layer of the original DVR family.

The new module `HC4/Valuation/CanonicalSmithReesSpecialFiber.lean` constructs the correct
second one-parameter family using the already-formalised integral Smith conformal action.

Main results:

* `constantFamily_hasIntegralCanonicalSmithConformalDivisibility` proves the canonical
  `(2,2)` Smith deformation is integral whenever the symmetric separator is nonnegative on
  support.
* `canonicalSmithCoefficientQuotient_eq` removes the `Classical.choose` ambiguity and
  identifies every supported quotient coefficient explicitly as
  `X^(rawExponent - 4) * C(coeff)`.
* `polynomialFamilySpecialFiber_canonicalSmithReesFamily` proves the special fibre of that
  deformation is exactly `canonicalSpecialFiberSmithPolynomial F`.
* `CanonicalSmithLosslessFrontier.degree_two_le` derives `2 ≤ D` from the already-retained
  nonzero persistent quadratic packet and homogeneity, avoiding an invasive frontier change.
* `CanonicalSmithLosslessFrontier.specialFiber_symmetricDelta_nonnegative` derives the
  separator nonnegativity from the existing homogeneous exact-axis-collision Smith shape
  theorem.
* `CanonicalSmithLosslessFrontier.specialFiber_smithReesFamily_eq_packet` and the departure
  wrapper expose the retained packet as the actual special fibre of the honest Smith-Rees
  family.

`FirstSchurDepartureBridge.lean` imports this module so the next phase can build the Schur
clock from the correct Smith parameter without another plumbing patch.

No `sorry`, `admit`, or `unsafe` is introduced.
