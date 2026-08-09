# Phase 81 changelog

## Goal

Replace the finite part of the manuscript statement
"a nonconstant rational map P¹ → P¹ is surjective" by a direct algebraic
certificate suited to Lean.

## Added

For a reduced fraction `N / D` over an algebraically closed field:

1. a root of `N - C y * D` cannot also annihilate `D` when `N,D` are coprime;
2. every nonconstant fibre polynomial therefore gives a genuine finite
   preimage of `y`;
3. noncancellation of the coefficient at `natDegree D` certifies that the
   fibre polynomial is nonconstant;
4. every scalar except
   `N.coeff D.natDegree / D.leadingCoeff` has a finite preimage;
5. those finite target values plus the exceptional one-point infinity chart
   form the existing `TwoChartCover`.

## Scope

This phase does not yet prove denominator removal for the autonomous
right-hand side.  It provides the finite-target coverage needed for that
next bridge.  The infinity value still needs its ODE certificate in the
following phase.


## Phase 81.1
- Fixed the single Phase 81 compile error in `eval_denominator_ne_zero_of_isCoprime_sub_eval_zero`.
- No theorem statements or mathematical content changed.
