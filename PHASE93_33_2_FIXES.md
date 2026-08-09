# Phase 93.33.2 — explicit Fin 4 linear-part coefficient expansion

Affected module:

    HC4/Newton/PositiveWeightTriangularEvaluation.lean

The Phase 93.33.1 build shows that the remaining failures are entirely in
the two coefficient lemmas for `fourVariableLinearPart`.

The simplifier does not unfold the dependent finite sum

    ∑ j : Fin 4, monomial (single j 1) ...

far enough on its own.

## Repair

For the degree-one coefficient theorem, split the queried coordinate by
`fin_cases` and explicitly expand the four-term sum with

    Fin.sum_univ_four.

The previously introduced `single_one_eq_iff` then closes all off-diagonal
one-hot exponent comparisons.

For the non-single coefficient theorem, likewise expand the finite sum
with `Fin.sum_univ_four`.  The hypotheses

    single j 1 != m

then eliminate all four monomial contributions directly.

No evaluation theorem, endpoint theorem, statement, or hypothesis changes.
No heartbeat limits are raised.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
