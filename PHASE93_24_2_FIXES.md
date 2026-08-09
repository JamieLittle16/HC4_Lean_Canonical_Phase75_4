# Phase 93.24.2 — name the post-derivative exponent

Affected file:

    HC4/Newton/TerminalActualHessian.lean

The Phase 93.24.1 compiler reached the intended derivative formula, but the
pinned elaborator could not reliably parse/application-elaborate expressions

    (d - Finsupp.single j 1) i

inside casts and local hypotheses.

This repair introduces the intermediate exponent

    dAfterJ : σ →₀ ℕ := d - Finsupp.single j 1

and rewrites the local proof entirely in terms of `dAfterJ`.

The two facts obtained from the nonzero monomial Hessian contribution are
now stated unambiguously as

    coeff d F * (d j : K) * (dAfterJ i : K) != 0

and

    dAfterJ - single i 1 = 0.

The existing coordinate argument then proves the exponent is exactly
`quadraticExponent i j`.

This is only an elaboration repair.  No theorem statement or mathematical
hypothesis changes.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
