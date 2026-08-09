# Phase 93.24.1 — constant-term monomial API repair

Affected file:

    HC4/Newton/TerminalActualHessian.lean

The Phase 93.24 failure occurs after `MvPolynomial.eval_zero'` has already
reduced the evaluated monomial to `MvPolynomial.constantCoeff (...)`.

The proof then incorrectly attempted to rewrite with

    MvPolynomial.coeff_monomial,

which applies to `MvPolynomial.coeff`, not to `constantCoeff`.

The repair replaces that line with

    MvPolynomial.constantCoeff_monomial.

Its conclusion is exactly the required conditional:

    constantCoeff (monomial d r) = if d = 0 then r else 0.

The remainder of the proof already analyses this `if`, so no other proof
or theorem statement changes are needed.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
