# Formalisation status through Phase 84.1

Phase 83.1 is locally kernel-green according to the user.

Phase 84 introduces canonical reduced numerator/denominator pairs for the logarithmic source and the explicit rank-three target using Mathlib `RatFunc.num`/`RatFunc.denom`.

Phase 84.1 fixes the initial notation-scope elaboration failure by replacing scoped `K[X]` notation with explicit `Polynomial K`. The patch is a candidate until the user's pinned Lean 4.24 / Mathlib checkout passes `./verify.sh`.
