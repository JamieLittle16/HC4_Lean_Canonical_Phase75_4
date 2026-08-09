# Phase 93.26 — terminal direct-rank-jump reduction

This is a larger terminal-endpoint tranche built against the user-supplied
green Phase 93.25 checkpoint.

## 1. `TerminalCollision.lean`

Adds the generic final contradiction:

    distinct exact gradient collision
    + injective terminal gradient
    -> False.

No valuation formalism is built into this lemma.

## 2. `TerminalScalarGradient.lean`

Closes the scalar terminal branch.

From `HasPureQuadraticSupport`, Lean derives ordinary homogeneity of degree
two.  Euler's identity applied to each first derivative gives the exact
linear formula

    grad F(p) = vecMul p (Hess F(0)).

For the standard four terminal coordinates, the actual Hessian from Phase
93.24 agrees with this matrix.  Nonzero determinant makes `vecMul`
injective via Mathlib's matrix nonsingularity API.

Consequently:

    scalar terminal weight
    + nontrivial weight
    + weighted homogeneity
    + nondegenerate actual Hessian
    -> injective gradient.

A distinct exact collision therefore rules the scalar terminal branch out
completely.

## 3. `TerminalCenteredWeights.lean`

For the non-scalar branch define

    mu_i = 2 lambda_i - d.

A nonzero quadratic coefficient gives `mu_i + mu_j = 0`.

Because a nondegenerate four-by-four Hessian has a nonzero entry in every
row, every coordinate has an opposite centred-weight partner.

Non-scalarity forces at least one centred weight to be nonzero.  Hence the
terminal face contains a distinct pair of coordinates with nonzero opposite
centred weights.

## 4. `TerminalDirectRankJumpReduction.lean`

Packages the exact remaining terminal alternative.

Without using a collision:

    terminal conformal face
    -> injective gradient
       OR residual non-scalar opposite-pair branch.

With a distinct exact collision, injectivity is impossible, so every
surviving terminal direct-rank-jump obstruction is forced into the explicit
residual branch.

This phase deliberately does NOT claim that the non-scalar endpoint is
already solved.  It closes the scalar direct jump and reduces the remaining
terminal problem to a much sharper opposite-weight configuration.

No theorem statement from earlier phases is weakened.
No proof escape hatch or new axiom is introduced.
