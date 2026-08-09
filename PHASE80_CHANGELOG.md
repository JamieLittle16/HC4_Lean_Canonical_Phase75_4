# Phase 80 — autonomous ODE translation bridge

Phase 80 connects the green polynomial pole-order theorem to the unshifted
polynomial autonomous equation.

New file: `HC4/Polynomial/AutonomousODETranslation.lean`.

Main results:

- `derivative_translatePolynomial`
- `shiftedEuler_translatePolynomial`
- `shiftedEtaNumerator_translatePolynomial`
- `shiftedAutonomousClearedRHS_translatePolynomial`
- `shiftedPolynomialAutonomousLogODE_translate`
- `natDegree_le_two_of_polynomialAutonomousLogODE_after_translation`

No rational-denominator removal is claimed in this phase.  The remaining
rank-three autonomous bridge is to obtain the polynomial autonomous equation
from the explicit rational rank-three formula, then supply the standard
nonzero-root multiplicity factorisation.
