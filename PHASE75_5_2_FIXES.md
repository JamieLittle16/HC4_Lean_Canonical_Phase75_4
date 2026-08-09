# Phase 75.5.2 — `sum_eq_single` fallback fix

Repairs the final side-condition in
`coeff_mul_eq_constant_mul_of_right_vanishes_below`.

`Finset.sum_eq_single` asks for the summand to vanish in the hypothetical
case that the distinguished index `(0,j)` is not in `Finset.antidiagonal j`.
But `(0,j)` is always in that antidiagonal.  The proof now establishes that
membership explicitly and eliminates the contradictory fallback hypothesis.

No theorem statements or mathematical interfaces are changed.
