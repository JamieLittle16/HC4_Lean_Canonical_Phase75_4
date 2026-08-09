# Phase 93.31 — determinant-matched positive-weight triangularity

Built against the clean Phase 93.30.2 tree.

The standard two-zero branch is green and closed under JC2.  This phase
turns to the k=0 / strictly-positive endpoint.

## TerminalPermutedGradient

Phase 93.27 gives a complement permutation

    lambda (pi i) + lambda i = d.

Define

    G_i = pderiv (pi i) F.

The file proves that `G_i` has weighted degree `lambda i`, so `G` is
weight-preserving.  It also proves exact injectivity equivalence between
the permuted-gradient evaluation map and the original gradient.

This removes the need to postulate the manuscript's fixed hyperbolic
involution at this stage: the determinant matching itself supplies the
output permutation.

## PositiveWeightTriangularSupport

For strictly positive weights and a weighted-homogeneous component of
degree `t`, every supported variable has weight <= t.

If a supported variable already has weight t, positivity forces the
monomial to be exactly that single linear variable.

Hence every supported monomial satisfies the exact dichotomy

    X_j with lambda_j = t

or

    every occurring variable has weight < t.

At a minimum positive weight, the lower alternative is impossible, so the
component is supported purely on same-weight linear variables.

## TerminalPositiveWeightTriangularReduction

Applies the preceding theorem to the determinant-matched terminal gradient.

The strictly-positive terminal branch now has an explicit triangular
weight-preserving polynomial map whose nonlinear terms use only lower-weight
variables.

The next phase should combine this with invertibility of the linear part
(which follows from the terminal Hessian determinant) and induct over the
finitely many weights to prove injectivity.  Because the permuted gradient
is injective iff the original gradient is injective, that will close k=0.

No general torus theorem is used.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
