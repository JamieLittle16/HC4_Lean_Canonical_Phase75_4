# Phase 89.1 — finite lexicographic refinement core

## New verified target

Adds `HC4.Newton.LexicographicRefinement`.

The core theorem is:

    isScaledMaxOn_iff_isLexMaxOn

For a finite support `S`, if every secondary weight is `< M`, the maximisers
of the single weight

    M * w₀ + w₁

are exactly the lexicographic maximisers of `(w₀,w₁)`.

This is the finite domination mechanism needed to replace an iterated
Newton/Rees refinement by a single exposed weight.

## Why this phase is deliberately abstract

The theorem is first proved at the level of finite supports and natural
weights, independent of `MvPolynomial`. This keeps the genuinely
mathematical ordering argument separate from the project's existing
`initialForm` representation. Phase 89.2 can then specialise it to
`HC4.Polynomial.WeightedInitial`.

## Build integration

`RankThreeInfinityAssembly.lean` receives one additional import of the new
module so the existing canonical `./verify.sh` necessarily kernel-checks
Phase 89.1. The new module itself has no dependency on RationalRigidity, so
this creates no proof cycle.

No theorem statement from Phase 88 is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
