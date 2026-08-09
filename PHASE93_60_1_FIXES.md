# Phase 93.60.1 — Evaluation/map API fix

The first 93.60 build exposed two connected Mathlib proof-shape issues.

1. `MvPolynomial.map_eval` is not available under that name in the pinned
   Mathlib version.  `eval_parameterRamificationFamily` is now proved
   directly by `MvPolynomial.induction_on`; constants, sums, and
   `p * X n` all reduce by simp.

2. In the collision transport theorem the outer definition
   `parameterRamificationFamily` hid the `MvPolynomial.map` expression from
   `MvPolynomial.pderiv_map`.  The proof now unfolds the family map first,
   rewrites the derivative, changes back to the packaged family form, and
   invokes the newly direct evaluation theorem.

No theorem statement or mathematical content is changed.
