# Phase 93.35.1 — affine recovery API and simplification repair

Affected module:

    HC4/Newton/TerminalOneZeroAffineRecovery.lean

The Phase 93.35 build accepted the substantive unit-to-constant slope step.
The remaining failures were local Lean API/proof-shape issues.

## 1. Constant-polynomial coefficient orientation

In the nonzero exponent branch of

    finFour_eq_C_of_all_pderiv_eq_zero

the simplifier needed the reverse inequality

    0 != m

rather than only

    m != 0.

The repair records it explicitly from `hm`.

## 2. Partial derivative of subtraction

`MvPolynomial.pderiv i` is a bundled derivation.  There is no theorem named

    MvPolynomial.pderiv_sub

in this pinned Mathlib API.

The generic bundled-map theorem

    map_sub

is used instead in all four derivative calculations.

## 3. Closed calc branch

After rewriting by `hRconst`, the second calc branch is already closed.
The redundant trailing `rfl` is removed.

## 4. Affine evaluation rewrite

A single

    rw [hA] at hgrad1

rewrites both occurrences of `pderiv 1 F` in the equality.  The previous
second rewrite therefore failed because no occurrence remained.

No theorem statement, mathematical hypothesis, heartbeat setting, or
proof strategy changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
