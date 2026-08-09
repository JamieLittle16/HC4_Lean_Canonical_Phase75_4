# Phase 93.22.1 — Finsupp weighted-degree repair

Affected file:

    HC4/Newton/TerminalConformalWeight.lean

Two local proof repairs only.

## Quadratic weighted degree

The generic simplifier could not evaluate

    (single i 1 + single j 1).sum ...

because it had to account for the diagonal case `i = j`.

The proof now splits explicitly:

* if `i = j`, merge the two singletons using `Finsupp.single_add`,
  obtaining a single coefficient `2`, then simplify;
* if `i != j`, evaluate the two-point sum using the long-standing theorem
  `Finsupp.sum_single_add_single`.

This proves exactly the same identity

    wt(X_i X_j) = lambda_i + lambda_j.

## Constant weight factorisation

`rw [Finset.sum_mul]` already closes the goal after unfolding the two
weighted-degree definitions.  The later `Finset.sum_congr` proof block was
therefore unreachable and caused `No goals to be solved`; it has been
removed.

No theorem statement or mathematical content changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
