# Phase 93.70.1 — section quotient / arithmetic cleanup

The first Phase 93.70 build exposed a small collection of proof-engineering
issues.  This patch fixes them without changing the mathematical
dispatcher.

## Exact order zero

The primitive zero-grade lemma now derives the exact polynomial parameter
order by composing the already-proved
`smithFamilyCoefficientOrder_eq` equality with the hypothesis, rather than
asking `omega` to reason through the definition.

## Coefficient margin

`separatedSectionWall_coefficient_margin_one` has been rewritten without
local `let` abbreviations.  This removes the cluster of `dsimp made no
progress` failures and leaves the four arithmetic cases directly in the
syntax expected by `omega`/`nlinarith`.

## Section quotient proofs

Three section lemmas no longer manipulate `Classical.choose_spec` directly.

They now use the green identity

    smithConformalInflateSection_integralSection_eq

and take its coordinate with `congrFun`.  This gives the stable exact
equation

    X^sourceExponent * integralSectionCoordinate
      = ramifiedOriginalCoordinate.

It is used to prove:
- strict-before-wall => zero special value;
- identically-zero coordinate => zero quotient coordinate;
- coordinate zero preserves its constant coefficient.

This removes all dependent-choice rewrite failures.

## First-wall non-wall section theorem

The generic theorem now accepts the integral-section divisibility proof as
an explicit argument instead of constructing it inside its result type.
This removes the out-of-scope `a`/`b` elaboration failures.

The equality between the local abbreviation `N` and the genuine first wall
is also converted explicitly before using section-wall membership.

No theorem statement at the headline dispatcher level changes.
No `sorry`, `admit`, `axiom`, or `unsafe` occurs in the Lean source.
