# Phase 93.35.2 — isolate affine recovery from two-zero simp aliases

Affected module:

    HC4/Newton/TerminalOneZeroAffineRecovery.lean

The Phase 93.35.1 build shows that the unit-to-constant slope theorem,
the zero/one derivative calculations, and the characteristic-zero
constant-remainder argument have progressed past their previous failures.

Only the `2` and `3` derivative calculations fail.

## Cause

Imported two-zero simp lemmas rewrite

    pderiv 2 P  -> standardTwoZeroA P
    pderiv 3 P  -> standardTwoZeroC P

before

    rw [map_sub]

can expose the subtraction inside

    pderiv 2 (A - C s * X 0)
    pderiv 3 (A - C s * X 0).

The resulting goals mention `standardTwoZeroA/C` and no longer match the
generic map-subtraction rewrite.

## Repair

Disable exactly those two simp lemmas in this one-zero module:

    attribute [-simp] standardTwoZero_pderiv_two_eq_A
    attribute [-simp] standardTwoZero_pderiv_three_eq_C

This is the same scoped isolation already used successfully in
`TerminalOneZeroHessianFactor`.

No theorem statement, mathematical hypothesis, or proof strategy changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
