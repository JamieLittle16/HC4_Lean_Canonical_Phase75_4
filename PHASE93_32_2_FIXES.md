# Phase 93.32.2 — remove redundant mixed-partial rewrite

Affected module:

    HC4/Newton/TerminalPositiveWeightLinearBlocks.lean

The Phase 93.32.1 build shows that after unfolding the relevant
definitions, Lean's goal is already

    eval 0 (pderiv j (pderiv (pi i) F))
      =
    coeff (single j 1) (pderiv (pi i) F).

This is exactly the statement of

    eval_zero_pderiv_eq_linearCoeff
      (pderiv (pi i) F) j.

Therefore no mixed-partial commutation is required at all.

The repair simply removes the redundant `rw [pderiv_comm_backport ...]`
and applies the helper theorem directly.

No theorem statement or hypothesis changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
