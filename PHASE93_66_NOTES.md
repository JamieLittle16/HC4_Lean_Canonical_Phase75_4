# Phase 93.66 — Exact parameter order and aligned Smith walls

Built over the green Phase 93.65 tree.

This phase replaces the rational repeated-denominator issue by a single
integer wall lattice.

## Exact X-adic order

For every nonzero `c : K[tau]`:

- `polynomialParameterOrderCandidates c hc` is the finite set of all
  `n <= natDegree c` such that `X^n | c`;
- `polynomialParameterOrder c hc` is its maximum;
- the selected power divides `c`;
- `X^(order+1)` does not divide `c`;
- the chosen primitive quotient has nonzero constant coefficient.

This is the exact polynomial analogue of the maximal finite extraction
used successfully in Phase 93.58.

The order is also exposed directly for genuine multivariate-family
coefficients in support.

## Symmetric derivative arithmetic

The canonical Smith derivative is proved to be

    delta(e) = 2 * (b + c + 2*d - 2).

Hence it is even.  Together with the already-green lower bound
`delta >= -4`, every negative derivative is exactly `-4` or `-2`.

## Why ramification 20

A single fixed ramification by `20` aligns every possible wall:

Coefficient walls:
- delta = -4 -> N = 5*v
- delta = -2 -> N = 10*v

Section walls:
- y/z weight 2 -> N = 10*v
- w weight 4 -> N = 5*v

All wall positions are natural numbers.

The phase proves the exact wall equalities and nonnegativity before each
wall, plus an `Option Nat` coefficient-wall selector.

## Next construction

Phase 93.67 can now define a finite maximal legal integer step `N` using:

- exact coefficient orders from this phase;
- exact nonzero moving-section orders;
- an explicit finite cap derived from coefficient orders and Hessian defect.

At maximal `N`, one of three things must happen:

1. a negative Smith coefficient hits value zero -> the transformed special
   fibre has a nonpositive Smith grade;
2. a moving section hits its weight boundary -> terminal degeneration;
3. the artificial cap is reached -> either a zero-grade coefficient is
   forced onto the minimal face, or the accumulated common factor exceeds
   the Hessian-defect budget.

This is the scale-safe maximal-normalisation route.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
