# Phase 93.33.1 — one-hot coefficient simplification and residual cancellation

Affected module:

    HC4/Newton/PositiveWeightTriangularEvaluation.lean

The Phase 93.33 build reached the new evaluation layer.

## One-hot exponent injectivity

The simplifier did not know that

    Finsupp.single i 1 = Finsupp.single j 1

forces `i = j`.

The repair adds the finite-coordinate helper

    single_one_eq_iff

proved by evaluating both Finsupps at coordinate `i`.

The linear-part coefficient theorem can then simplify directly, and the
non-single coefficient theorem uses the symmetric form of the supplied
`m != single j 1` hypotheses.

## Residual cancellation before linear expansion

The original proof expanded

    P = R + L

too early.  That reintroduced coefficients of `R` into the final algebraic
goal even though the key fact

    eval p R = eval q R

was already available.

The repaired proof first derives

    eval p P - eval q P
      =
    eval p L - eval q L

using only `P = R + L` and residual evaluation equality.  Only then is the
linear part expanded.

This keeps the final ring goal entirely in the linear coefficients of `P`
and avoids any residual-coefficient bookkeeping.

No theorem statement or mathematical hypothesis changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
