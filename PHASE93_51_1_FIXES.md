# Phase 93.51.1 — Pointed restart parse fix

Lean parsed

    r ≠ fun _ => (0 : K) ∧ ...

with the conjunction inside the lambda body, producing a type mismatch
(`And 0`) and preventing the theorem from being declared.

This patch changes only the theorem statement to

    r ≠ (fun _ => (0 : K)) ∧ ...

The later `unknown identifier` and terminal proof failure were cascading
errors caused by the failed declaration.

No mathematical content or theorem intent is changed.
