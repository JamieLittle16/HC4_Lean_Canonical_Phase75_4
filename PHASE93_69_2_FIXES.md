# Phase 93.69.2 — dependent rewrite/cancellation fix

The 93.69.1 build reduced the endpoint file to seven local elaboration
errors.  None changes the mathematical construction.

## Proof-indexed primitive parts

`polynomialParameterPrimitivePart c hc` depends on both `c` and the proof
`hc : c != 0`.  Rewriting `c` inside expressions containing these dependent
proofs creates an ill-typed rewrite motive.

Both source-coefficient and section-coordinate ramification factorizations
now use a `calc` chain and `congrArg parameterRamificationHom` on the exact
primitive factorization, followed by ordinary `map_mul`/power algebra.

## Zero residual local order

The local abbreviation

    v := smithFamilyCoefficientOrder P d

is definitionally the expression already present in `hzero`.  The proof now
uses `change ... v ... at hzeroV` rather than rewriting a different
proof-indexed parameter-order term.

## Wrapper simplification

Two `dsimp only` calls after unfolding the left/right genuine-wall section
definitions made no progress and have been removed.

## Minimal zero-grade order

The exact parameter-order equality is now composed explicitly:

    parameterOrder = smithFamilyCoefficientOrder = m.

This avoids a rewrite whose syntactic pattern was not present.

## Cancellation orientation

The final `X^(4*N)` cancellation in the minimal zero-grade coefficient
theorem produced the equality opposite to the theorem target.  The result
is now reversed explicitly with `.symm`.

No theorem statement or mathematical assumption changes.
No `sorry`, `admit`, `axiom`, or `unsafe` occurs in the Lean source.
