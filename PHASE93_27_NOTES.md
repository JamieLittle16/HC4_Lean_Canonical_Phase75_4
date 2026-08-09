# Phase 93.27 — terminal weight matching and planar JC2 endpoint interface

Built against the clean Phase 93.26.1 tree.

## TerminalWeightPermutation

Uses the exact Leibniz determinant formula.  A nonzero 4x4 determinant has
a permutation term whose four selected entries are all nonzero.  For the
terminal actual Hessian each selected entry gives a nonzero quadratic
coefficient, hence the complement-weight equation

    lambda_(pi i) + lambda_i = d.

Equivalently, the centred weights are globally paired by an opposite-weight
permutation.

This is stronger than the earlier row-by-row partner theorem.

## TerminalNonnegativeWeights

Introduces the geometric Smith-lattice hypothesis

    lambda_i >= 0.

For a non-scalar terminal conformal face Lean derives:

* d > 0;
* 0 <= lambda_i <= d for every coordinate;
* a zero coordinate is matched to a coordinate of weight exactly d;
* the terminal weights split into a strictly-positive interior or a
  zero-weight boundary.

The later restart adapter should prove this nonnegativity from Smith normal
form rather than postulate it globally.

## PlanarJC2Interface

Introduces an explicit Lean representation of the exact JC2 consequence
needed by the HC4 reduction:

    PlanarJC2Injectivity K

means that every two-component polynomial map with nonzero constant
Jacobian determinant is injective.

The Jacobian determinant is written directly from the four partial
derivatives, avoiding matrix-polynomial API dependencies.

## PlanarDoublingInjectivity

Proves the function-level Hessian-doubling mechanism:

    (u,v) |-> (v^T J(u) + dD(u), G(u))

is injective when G is injective and every J(u) has nonzero determinant.

Thus once the two-zero terminal support is identified with the doubling
normal form, JC2 supplies exactly the missing base injectivity and the
4-dimensional terminal gradient is injective.

No endpoint classification is assumed in these modules.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
