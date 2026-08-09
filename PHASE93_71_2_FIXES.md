# Phase 93.71.2 — arithmetic closure fix

The Phase 93.71.1 build leaves only three errors.

## 1. Positive residual inequality

`omega` was seeing both

    N * (raw - 4)

and

    N * raw

as separate nonlinear atoms.

The proof now inserts the explicit integer ring identity

    20*v + N*(raw - 4)
      = N*raw + 20*v - 4*N

before invoking `omega`, then casts the resulting integer inequality back
to naturals.

This is the same robust normalization pattern used successfully in the
earlier aligned-Smith phases.

## 2. z-gradient

The final `simp` already solves the explicit z-gradient goal, so the
subsequent `ring_nf` caused `No goals to be solved`.  It is removed.

## 3. Longitudinal coefficient

After simplifying the x-gradient collision, Lean returns the branch

    D = 0

at the natural-number level, not `(D : K) = 0`.

The proof now obtains `D != 0` directly from `2 <= D` and eliminates that
branch before accepting `A = 0`.

No theorem statements or assumptions change.
No `sorry`, `admit`, `axiom`, or `unsafe` occurs in the Lean source.
