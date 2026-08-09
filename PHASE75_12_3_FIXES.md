# Phase 75.12.3 — Additive numeral derivative fix

Replaces the failed attempt to rewrite the numeral polynomial `2` as an
`MvPolynomial.C` term.  Instead, prove `2 = 1 + 1` in the multivariate
polynomial ring, use additivity of the bundled partial derivation, and finish
with `MvPolynomial.pderiv_one`.

No theorem statements, assumptions, axioms, `sorry`, `admit`, or `unsafe`
constructs are introduced.
