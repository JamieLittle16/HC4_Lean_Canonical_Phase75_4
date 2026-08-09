# Phase 93.34.2 — isolate the one-zero Hessian simplifier

Affected module:

    HC4/Newton/TerminalOneZeroHessianFactor.lean

The Phase 93.34.1 build reached the one-zero Hessian matrix-identification
theorem.  Two entries failed because imported two-zero `[simp]` lemmas
rewrote

    pderiv 2 F  -> standardTwoZeroA F
    pderiv 3 F  -> standardTwoZeroC F

before the one-zero proof could commute mixed partials.

That changed the intended goals

    pderiv 1 (pderiv 2 F) = 0
    pderiv 1 (pderiv 3 F) = 0

into irrelevant goals involving `standardTwoZeroA/C`.

The repair disables exactly those two simp lemmas in this module:

    attribute [-simp] standardTwoZero_pderiv_two_eq_A
    attribute [-simp] standardTwoZero_pderiv_three_eq_C

The mixed-partial step can then expose the already-proved sparse row:

    pderiv 2 (pderiv 1 F) = 0
    pderiv 3 (pderiv 1 F) = 0.

No theorem statement or mathematical hypothesis changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
