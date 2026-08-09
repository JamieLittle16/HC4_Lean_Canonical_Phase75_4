# Phase 75.10.2 — Targeted Special-Fibre Normalisation Fix

This patch repairs the remaining coefficientwise packet-exposure proof in
`HC4/Valuation/CanonicalSmithDefectExposure.lean`.

The prior proof globally unfolded `polynomialFamilySpecialFiber` in the goal.
That simultaneously unfolded the *exposure* special fibre on the left and the
*original-family* special fibre inside the canonical Smith packet on the right,
so branch facts such as `hmem`, `hnot`, and `hcoeffSpecial` no longer matched
syntactically.

The fix adds a local coefficient theorem

`coeff_polynomialFamilySpecialFiber`

and rewrites only the coefficient of the exposure special fibre.  The original
special fibre remains in its named form throughout the Smith-subface case
split.  In the zero-separator branch the same helper is used explicitly to
identify the surviving packet coefficient.

No theorem statements, assumptions, axioms, `sorry`, `admit`, or `unsafe`
constructs are added.
