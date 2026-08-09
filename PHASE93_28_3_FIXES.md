# Phase 93.28.3 — differentiate the doubling identity without broad rewriting

Affected module:

    HC4/Newton/TerminalTwoZeroDoublingForm.lean

The Phase 93.28 build reached the two base-coordinate derivative formulas,
but

    rw [hform.1]

rewrote every occurrence of `F`, including the occurrences hidden inside

    standardTwoZeroA F = pderiv 2 F
    standardTwoZeroC F = pderiv 3 F.

That recursively expanded the coefficient polynomials and produced the
large spurious higher-derivative goals seen in the compiler output.

The repair differentiates the normal-form equality itself:

    congrArg (MvPolynomial.pderiv 0) hform.1

and similarly for coordinate `1`.

Thus only the intended polynomial identity

    F = X₂ A + X₃ C

is differentiated.  Simplification then uses the facts that `pderiv 0 X₂`,
`pderiv 0 X₃`, `pderiv 1 X₂`, and `pderiv 1 X₃` vanish.

No positive-positive Hessian vanishing is needed for these formulas.
No theorem statement or mathematical hypothesis changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
