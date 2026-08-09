# Formalisation status — Phase 77.1 candidate

Phase 76 was reported green by the user and connects the rank-three
line-moment Hessian to the autonomous scalar equation.

Phase 77.1 is the repaired candidate for the quadratic autonomous ODE
coefficient-rigidity layer.  If green, it verifies:

- the least positive coefficient forces the linear autonomous coefficient
  `B = m`;
- the top coefficient forces `A * natDegree(phi) + B = 0`;
- the `A = -1` case is two-term;
- the positive reciprocal `A = 1/(J-1)`, `J >= 2`, case is impossible.

The remaining conceptual rank-three ODE obligation is still the specialised
pole-order/quadraticity bridge ruling out rational-map degree at least three,
plus assembly from the explicit Phase-76 rational function to the asymptotic
coefficients used here.

No claim is made that the complete symmetric-gradings theorem is yet
formalised.
