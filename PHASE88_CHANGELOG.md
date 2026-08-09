# Phase 88 changelog

## New: `HC4/RationalRigidity/ClearedInfinityEvaluation.lean`

Introduces `clearedPolynomialSubstitution`, the finite polynomial
homogenisation of `P(N/D)` to a common denominator degree.

Candidate results include:

- `clearedPolynomialSubstitution_natDegree_le`
- `coeff_clearedPolynomialSubstitution_top`
- `clearedPolynomialSubstitution_map_eq`
- `clearedPolynomialSubstitution_identity_of_ratFunc`
- `eval_at_infinity_eq_zero_of_autonomous_ratFunc_identity`
- `ratFunc_transcendental_of_denom_natDegree_pos`

The main coefficient theorem says that, for equal-degree reduced source
numerator/denominator with monic denominator, the top coefficient of the
cleared substitution is exactly evaluation at the source infinity value.

## New: `HC4/RationalRigidity/RankThreeInfinityAssembly.lean`

Combines Phases 83--87 to remove the remaining explicit infinity hypothesis
from the rank-three target-denominator theorem.

Candidate endpoints include:

- `rankThreeTargetNumerator_eval_infinity_eq_zero`
- `rankThreeTargetDenominator_constant_auto`
- `rankThreeTargetDenominator_constant_of_fraction_equation_auto`
- `rankThreeTargetDenominator_constant_of_core_det_zero_auto`
- `exists_rankThree_polynomial_autonomous_equation`
- `exists_rankThree_polynomial_autonomous_equation_of_fraction_equation`
- `exists_rankThree_polynomial_autonomous_equation_of_core_det_zero`

Thus the intended end-to-end conclusion of this phase is:

`singular rank-three fraction core`
→ `canonical target denominator is a nonzero constant`
→ `eta = R(rho)` for an explicit polynomial `R`.

This is the rational-to-polynomial half of the manuscript autonomous lemma;
the polynomial degree-≤2 handoff to Phase 79 remains downstream.
