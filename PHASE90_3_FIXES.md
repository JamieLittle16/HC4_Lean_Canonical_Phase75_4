# Phase 90.3 — first Schur determinant order

## New module

    HC4/Newton/FirstSchurDeterminantOrder.lean

This phase proves the determinant-order step for the rank-two first-entry
branch without using coefficient-convolution formulas.

After factoring a common first parameter power `X^e` from the three entries
of a symmetric binary Schur family,

    A_e = X^e A,
    B_e = X^e B,
    C_e = X^e C,

Lean proves

    A_e C_e - B_e^2 = (X^e)^2 (A C - B^2).

Since `Polynomial K` is a domain and `X^e ≠ 0`, vanishing of the full
determinant forces the tail determinant to vanish identically. Evaluating
at `X = 0` then forces the determinant core of the first coefficient block
to vanish.

The packaged theorem

    FirstBinarySchurFamilyEntry.pivot_of_determinant_eq_zero

combines this determinant-order result with Phase 90.1: a nonzero first
binary coefficient in a determinant-zero family has the required rank-one
pivot certificate.

No existing theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
