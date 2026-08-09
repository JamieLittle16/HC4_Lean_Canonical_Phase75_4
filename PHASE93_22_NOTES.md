# Phase 93.22 — terminal conformal weight core

## New module

    HC4/Newton/TerminalConformalWeight.lean

With Phase 93.21 green, the restart audit leaves the terminal direct-rank
jump as the exceptional case to close before the final restart assembly.

This phase formalises the weight-theoretic half of the v5
`TerminalConformalFace` lemma.

It defines integral weighted homogeneity directly on the support of an
`MvPolynomial`.

Lean proves:

* the weighted degree of `X_i X_j` is `lambda_i + lambda_j`;
* every nonzero quadratic coefficient in a weighted-homogeneous terminal
  fibre satisfies `lambda_i + lambda_j = d`;
* for a constant nonzero weight `a`, the existence of one quadratic
  coefficient forces `d = 2a`;
* under that scalar weight, every supported monomial has ordinary degree
  exactly two.

The final predicate `HasPureQuadraticSupport` packages the scalar terminal
conclusion.

This closes the weight-combinatorics of the scalar terminal branch.
The next terminal phase should derive existence/nondegeneracy of the
quadratic part from the nonzero constant terminal Hessian determinant, then
combine that with this module to obtain the full scalar linear endpoint and
the non-scalar conformal cocharacter statement.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
