# Phase 91.12.1 — explicit MvPolynomial variable type repair

Affected file:

    HC4/Newton/RankTwoHomogeneousPacketClassification.lean

In the left-pivot `b = 0` branch, the proof needs to cancel the constant
polynomial `C q.a`.

Phase 91.12 wrote

    have hCa : MvPolynomial.C q.a ≠ 0 := ...

but `MvPolynomial.C q.a` does not determine the polynomial variable type
`σ`.  Lean 4.24 therefore left the variable type as a metavariable and
could not synthesize the polynomial instances.

Phase 91.12.1 pins the intended type explicitly:

    (MvPolynomial.C q.a : MvPolynomial σ K) ≠ 0

and the existing `mul_eq_zero` cancellation can then use it.

No theorem statement or mathematical content is changed.
The `hright` message is only an unused-variable linter warning.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
