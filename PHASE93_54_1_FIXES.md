# Phase 93.54.1 — Finsupp typing and dependent rewrite fix

This patch fixes the two root causes in the first Phase 93.54 compile.

## 1. Explicit Finsupp type

Lean could not infer the codomain of expressions such as

    d - Finsupp.single i 1

inside theorem statements and products.

Every derivative decrement is now written as

    d - (Finsupp.single i 1 : Fin 4 →₀ ℕ).

This removes the stuck `Field ?m` / "Function expected" metavariables.
The unknown helper theorem and later `sorry` warnings in the failed build
were cascading elaboration recovery from this error.

## 2. RHS-only expansion of `P`

The original

    rw [MvPolynomial.as_sum P]

attempted to rewrite `P` both on the right and inside the left-hand
dependent term

    integralKernelBlowupFamily kernel slope P hdiv,

where `hdiv` has a type depending on `P`.  Lean correctly rejected the
resulting rewrite motive.

Both derivative covariance proofs now use

    conv_rhs => rw [MvPolynomial.as_sum P]

so only the independent right-hand occurrence is expanded.

No theorem statement, construction, or mathematical argument is changed.
