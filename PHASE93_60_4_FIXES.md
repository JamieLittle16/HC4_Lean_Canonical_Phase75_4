# Phase 93.60.4 — Congruence-based induction fix

The 93.60.3 build showed that the remaining problem was forcing the packed
branch goals into an `eval₂` normal form with `change`.

This patch avoids that normalisation entirely.

## Add branch

The two induction hypotheses are combined directly with

    congrArg₂ (fun x y => x + y) hp hq

and the resulting equality is simplified into the `p + q` branch goal.

## `mul_X` branch

The induction hypothesis is multiplied on both sides by the ramified source
coordinate using

    congrArg (fun x => x * ramificationHom (a n)) hp

and then simplified into the `p * X n` branch goal.

This keeps the proof entirely in the packaged
`eval (parameterRamificationFamily ...)` form and avoids definitional-equality
assumptions about `MvPolynomial.map`/`eval₂`.

No theorem statement, assumption, or mathematical content changes.
