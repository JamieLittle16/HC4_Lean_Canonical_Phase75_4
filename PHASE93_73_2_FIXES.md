# Phase 93.73.2 — transvection signature fix

The Phase 93.73.1 build is now concentrated in three implementation
issues.

## 1. Longitudinal derivative branch

When the induction variable is coordinate `0`, the shear variable contains
an `if 0 = k`.

The hypothesis is stored as `k != 0`; simplification needs the reverse
orientation `0 != k`.

The branch now introduces

    hk0' : (0 : Fin 4) != k := Ne.symm hk0

before simplification.

## 2. Matrix transvection theorem signatures

The earlier calls to the `*_apply_same` lemmas omitted one of the
transvection indices.

The actual mathlib signatures are:

    transvection_mul_apply_same i j b c M
    mul_transvection_apply_same i j a c M

This patch supplies all arguments in the correct order.

For the left matrix `transvection 0 k c`:
- affected row is `0`;
- source row is `k`.

For the right matrix `transvection k 0 c`:
- affected column is `0`;
- source column is `k`.

The already-correct `*_apply_of_ne` calls are unchanged.

## 3. Constant coefficient

The final special-coordinate proof now converts

    Polynomial.constantCoeff (a 0) = 1

explicitly to

    (a 0).coeff 0 = 1

before rewriting the remaining polynomial coefficient expression.

No theorem statement or mathematical assumption changes.
No `sorry`, `admit`, `axiom`, or `unsafe` occurs in the Lean source.
