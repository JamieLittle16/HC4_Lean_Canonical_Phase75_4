# Phase 93.5.1 — Smith-grade arithmetic compatibility repair

Affected file:

    HC4/Newton/SmithGradeArithmetic.lean

Three pinned-version arithmetic issues are repaired.

## Surviving negative-coordinate lemmas

After the negative-coordinate shape theorem establishes `d = 0`, the
previous proof left that equality only as a hypothesis. `omega` therefore
did not normalize the other Smith grade tightly enough and allowed
spurious values below `-1`.

The repair performs

    subst d

and unfolds the remaining grade in both the exclusions and the goal before
calling `omega`.

## Positive product bound

The pinned Mathlib does not expose `Nat.mul_eq_one.mp` under that name.

Instead, from `1 <= l` and `k*l <= 1` Lean proves

    k = k*1 <= k*l <= 1,

so `k = 1`; symmetrically `l = 1`.

This uses only `Nat.mul_le_mul_left`, `Nat.mul_le_mul_right`, and
`Nat.le_antisymm`.

No theorem statement or mathematical content is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
