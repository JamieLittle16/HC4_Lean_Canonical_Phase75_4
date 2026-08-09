# Phase 93.32.1 — mixed-partial orientation repair

Affected module:

    HC4/Newton/TerminalPositiveWeightLinearBlocks.lean

The build reached the final theorem identifying the permuted Hessian entry
with the linear coefficient of the corresponding permuted-gradient
component.

After unfolding, the goal contains

    pderiv (pi i) (pderiv j F),

while `eval_zero_pderiv_eq_linearCoeff (pderiv (pi i) F) j` produces the
equivalent expression

    pderiv j (pderiv (pi i) F).

The original rewrite instantiated

    pderiv_comm_backport j (pi i) F,

whose left-hand side had the opposite orientation and therefore did not
transform the goal into the helper theorem's form.

The repair uses

    pderiv_comm_backport (pi i) j F

so the goal rewrites directly to the expected mixed-partial ordering.

No theorem statement or hypothesis changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
