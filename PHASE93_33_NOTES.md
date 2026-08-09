# Phase 93.33 — finite positive-weight recursion and endpoint closure

Built against the clean Phase 93.32.2 tree.

## PositiveWeightTriangularEvaluation

Introduces the full linear part of a four-variable polynomial and proves:

* removing it from a Phase 93.31 triangular component leaves only
  strictly-lower-weight monomials;
* a polynomial supported only in lower-weight variables evaluates equally
  at two points that agree in those lower-weight coordinates;
* therefore a triangular component satisfies the exact pointwise identity

      P(p) - P(q)
        =
      sum_j coeff(X_j,P) * (p_j - q_j).

For determinant-matched terminal-gradient components, Phase 93.32 identifies
those coefficients with the entries of the permuted terminal Hessian, so

    G_i(p) - G_i(q)
      =
    vecMul (p-q) L |_i

once p and q agree below weight lambda_i.

The file also defines the difference restricted to one terminal weight
slice and proves that, on an output of that weight, the full difference and
the slice give the same Hessian equation because all cross-weight entries
vanish.

## TerminalPositiveWeightEndpoint

Proves injectivity by strong induction on `natAbs (lambda i)`.

At weight t:

1. positivity makes all lower terminal weights have strictly smaller
   `natAbs`;
2. the induction hypothesis gives equality at all lower coordinates;
3. equal output values cancel the nonlinear terms and give the linear
   equations on the weight-t slice;
4. Phase 93.32's equal-weight block kernel theorem forces that slice to be
   zero.

Thus every coordinate agrees.

The resulting theorems are:

    positiveTerminalFace_permutedGradient_injective
    positiveTerminalFace_gradient_injective
    positiveTerminalFace_collision_impossible

If green, the entire strictly-positive (`k = 0`) terminal collision branch
is formally closed, independently of JC2 and without a general torus
classification.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
