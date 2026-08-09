# Phase 93.48 — Global restart descent

Built over the green Phase 93.47 assembly.

## Main result

This phase formalises the global lexicographic restart engine with state

    (determinant defect, finite local repair state).

A global step is either:

1. strict determinant-defect decrease; or
2. unchanged defect plus `RepairProgress`.

The main theorem

    globalRestartClassifier_reaches_terminal

uses nested strong induction:
- outer induction on determinant defect;
- inner induction on `RepairState.measure`.

Therefore a defect-lowering kernel blow-up may reset the local repair state
arbitrarily and termination is still guaranteed.

## Kernel-blow-up arithmetic interface

`HasPositiveKernelDefectDrop q s t` encodes

    0 < q,
    2*q <= s.defect,
    t.defect = s.defect - 2*q.

Lean proves this gives strict defect decrease and hence global restart
progress.

This exactly captures the arithmetic part of the handwritten kernel
blow-up formula `Delta' = Delta - 2q`.

## Scope boundary

This phase does NOT yet prove that an actual polynomial/DVR kernel blow-up:
- is integral;
- preserves the exact marked gradient collision;
- transforms the Hessian determinant by the required factor.

Those are the next valuation-algebra interfaces.  What is closed here is
the entire well-founded global induction once those exact geometric steps
are supplied.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
