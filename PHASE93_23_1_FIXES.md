# Phase 93.23.1 — local classical equality repair

Affected file:

    HC4/Newton/TerminalQuadraticHessian.lean

The Phase 93.23 build failed while elaborating

    terminalQuadraticHessianEntry

because its diagonal/off-diagonal definition tests `i = j` for an arbitrary
variable type `σ`, but no `DecidableEq σ` instance was in scope.

The definition is now explicitly `noncomputable` and introduces `classical`
locally before evaluating the equality test.

The later compiler warning saying a declaration used `sorry` was a
consequence of this failed elaboration: Lean had inserted an internal
placeholder for the broken definition.  The source patch itself contains no
`sorry`, `admit`, `unsafe`, or new axiom.

No theorem statement or mathematical hypothesis changes.
