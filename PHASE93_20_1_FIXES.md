# Phase 93.20.1 — pinned API repair for preterminal departure

Affected file:

    HC4/Newton/PreterminalFirstDeparture.lean

The Phase 93.20 failures were both convenience-API issues.

## Mixed partial commutation

The unavailable `MvPolynomial.pderiv_comm` theorem is no longer used.

The proof is now coefficientwise via the stable theorem

    MvPolynomial.coeff_pderiv.

If U=V the equality is reflexive.  If U!=V, the two coefficient formulas
simplify to the same coefficient of P multiplied by the same two scalar
factors in opposite order; commutative-ring normalisation closes the goal.

## Nonzero constant polynomial

Instead of relying on inference around `MvPolynomial.C`, the proof now
annotates the polynomial variable type explicitly and proves

    (MvPolynomial.C b : MvPolynomial σ K) != 0

by applying the zero-monomial coefficient map.  Equality to zero would
force b=0, contradicting the existing hypothesis.

No theorem statement or mathematical content changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
