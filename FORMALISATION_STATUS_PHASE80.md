# Formalisation status after Phase 80 candidate

## Candidate closure

Phase 80 removes the coordinate-translation hypothesis from the Phase-79
polynomial degree bound: an unshifted polynomial autonomous ODE transports to
the shifted ODE under `p(X) -> p(X + alpha)`.

This candidate is not kernel-verified until `./verify.sh` succeeds on the
user's pinned Lean 4.24 / Mathlib checkout.

## Still outstanding in rank-three branch

1. Reduce the explicit rational autonomous formula from the rank-three
   logarithmic Hessian to a polynomial autonomous right-hand side.
2. Extract a nonzero root and exact root-multiplicity factorisation for the
   translated polynomial.
3. Derive the manuscript infinity-leading-coefficient alternatives from the
   explicit rank-three numerator/denominator and connect them to Phase 77.
4. Assemble with the already-green binomial-pencil terminal contradiction.
