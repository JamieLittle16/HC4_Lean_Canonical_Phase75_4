# Phase 91.9 — finite recurrence classification

## New module

    HC4/Newton/LinearPowerRecurrenceClassification.lean

This phase combines the two green ingredients:

* Phase 91.7: uniqueness of the finite directional recurrence;
* Phase 91.8: the coefficient profile of `(v*X-u*Y)^n` satisfies it.

For `u ≠ 0`, the profile has nonzero left endpoint `(-u)^n`.  Hence for any
recurrence solution `c`, define

    a = c(0) / (-u)^n.

Lean proves

    c(k) = a * choose(n,k) * v^k * (-u)^(n-k)

for every `k ≤ n`.

The main theorem is

    directionalRecurrence_eq_linearPowerProfile

with existential and expanded-binomial variants.

This is the scalar finite-slice classification underlying the desired
HC4 packet form `a(X) * L(Y)^n`.  The next phase only needs to construct
the finite sequence `c(k)` from a frozen external multi-index of the
original `MvPolynomial` and invoke this theorem.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
