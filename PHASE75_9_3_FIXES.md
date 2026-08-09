# Phase 75.9.3 — Explicit impossible-clock branch

This surgical patch fixes the final reported goal in `CanonicalSmithReesSpecialFiber.lean`.

In the negative Smith-separator branch, the existing simplification reduces the coefficient statement to

```lean
0 = smithConformalRawExponent 2 2 d - 4 → MvPolynomial.coeff d F = 0.
```

The proof already knows

```lean
hraw_ne : smithConformalRawExponent 2 2 d - 4 ≠ 0.
```

The patch therefore introduces the impossible equality explicitly and eliminates it by contradiction, instead of expecting `simp` to use the reversed equality orientation automatically.

No theorem statement or assumption changes.
