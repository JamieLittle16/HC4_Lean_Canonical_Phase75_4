# Phase 82 changelog

## Added

`HC4/RationalRigidity/AutonomousDenominatorRemoval.lean`

New theorems:

- `eval_left_ne_zero_of_isCoprime_right_eval_zero`
- `constant_target_denominator_of_reduced_source_cover`

The main theorem assumes:

- a reduced source pair `N,D` with `D ≠ 0` and positive denominator degree;
- a reduced target pair `A,B`;
- a cleared autonomous identity at every finite source point;
- one cleared identity at the source infinity value.

It concludes `∃ b, b ≠ 0 ∧ B = C b`.

This is the algebraic pole-removal step needed between the green finite-preimage machinery and the polynomial autonomous ODE degree bound.
