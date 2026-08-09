# Phase 84.1 fixes

Phase 84 failed before elaborating the canonical reduced-fraction definitions because the scoped notation `K[X]` was not active in `CanonicalReducedFraction.lean`. Lean therefore parsed occurrences such as `K[X]` as `GetElem` indexing syntax; every later unknown-identifier error was a cascade from those failed declarations.

Phase 84.1 makes the representation bridge notation-independent:

- replaces every type occurrence `K[X]` by `Polynomial K`;
- replaces `algebraMap K[X] (RatFunc K)` by the explicit `algebraMap (Polynomial K) (RatFunc K)`;
- changes no theorem statement mathematically and changes no rational-function strategy.

The `RatFunc` API used by the file remains the canonical Mathlib one: `num`, `denom`, `isCoprime_num_denom`, `denom_ne_zero`, `monic_denom`, `num_div_denom`, and `denom_div_dvd`.
