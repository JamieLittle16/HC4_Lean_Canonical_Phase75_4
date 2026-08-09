# Phase 79 changelog

## Added

`HC4/Polynomial/AutonomousODEPolynomialDegree.lean`

Main definitions:

- `shiftedAutonomousClearedRHS`
- `ShiftedPolynomialAutonomousLogODE`

Main structural lemmas:

- `X_pow_mul_pow`
- `exists_shiftedEtaNumerator_factor`
- `exists_shiftedEta_mul_phi_pow_factor`
- `coeff_n_mul_e_add_two_shiftedEta_mul_phi_pow_zero`
- `coeff_n_mul_d_shiftedEuler_pow`
- `coeff_n_mul_j_add_e_shiftedEuler_pow_mul_phi_pow_zero`
- `coeff_n_mul_natDegree_shiftedAutonomousClearedRHS`

Main obstruction theorems:

- `no_shiftedPolynomialAutonomousLogODE_degree_ge_three`
- `natDegree_le_two_of_shiftedPolynomialAutonomousLogODE`

## Mathematical content

At a translated nonzero root

    phi = X^(n+1) q,  q(0) != 0,

the shifted Euler numerator starts in degree `n`, while the shifted eta
numerator starts in degree `2n`.

For an autonomous polynomial `R` of degree `d`, after clearing denominators,
the coefficient in degree `n*d` receives a nonzero contribution from the
leading `R` term. Every lower `R` term has an additional `phi` factor and
therefore begins later. If `d >= 3`, the eta side also begins later, at
`n*d + d - 2`. This is impossible.

Thus the autonomous polynomial has degree at most two.

## Phase 79.1

- fixed the single failing coefficient branch by changing `← mul_assoc` to
  `mul_assoc` before `Polynomial.coeff_C_mul`;
- no mathematical or API changes.
