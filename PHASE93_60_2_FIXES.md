# Phase 93.60.2 — Evaluation induction normal-form fix

The Phase 93.60.1 build showed exactly how Lean normalises the induction
branches.

## Evaluation theorem

Inside the `add` and `mul_X` branches, `parameterRamificationFamily`
unfolds to `MvPolynomial.map`, and evaluation of the mapped polynomial
normalises to `MvPolynomial.eval₂`.

The induction hypotheses are now explicitly `change`d to that same
`eval₂` normal form.  The branch goals are also stated in that normal form,
so they close by direct rewriting with the induction hypotheses.  This
avoids `simp` trying to cancel common factors and producing spurious
disjunctive goals.

## Collision theorem

A single

    rw [MvPolynomial.pderiv_map]

rewrites both ramified derivative occurrences in the equality.  The second
rewrite from Phase 93.60.1 was therefore targeting a pattern that no longer
existed and has been removed.

No theorem statement, assumption, or mathematical content changes.
