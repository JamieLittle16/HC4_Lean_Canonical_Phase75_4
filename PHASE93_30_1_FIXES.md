# Phase 93.30.1 — coordinate-normalise the two-zero gradient conjugacy

Affected module:

    HC4/Newton/TerminalTwoZeroGradientConjugacy.lean

The Phase 93.30 errors were all in the coordinate wrapper.

## Derivative through rename

After rewriting the ambient coefficient polynomial by `hA` / `hC`, the
goal already has the form

    pderiv (embedding i) (rename embedding A).

On the pinned Mathlib theorem, `pderiv_rename` rewrites this FORWARD to

    rename embedding (pderiv i A).

The previous proof used the reverse orientation, which could not match.

## Concrete Fin 2 coordinates

After `fin_cases`, Lean retained terms such as

    standardPositivePairEmbedding ((fun i => i) ⟨0,...⟩)

instead of reducing them definitionally before `rw`.

The repaired proof uses `change` to put each branch into its concrete form:

    pderiv 2 F
    pderiv 3 F
    pderiv 0 F
    pderiv 1 F

before invoking the Phase 93.28 derivative formulas.

This removes all dependence on reduction of the embedding wrappers.

## Final conjugacy

`Prod.ext` exposes the two projections of `doublingGradientMap`.
The first projection contains the harmless `+ 0` correction term, so the
two already-proved half-gradient identities are now imported with

    simpa [standardSplitPoint, HC4.doublingGradientMap]

rather than `exact`.

No theorem statement or mathematical hypothesis changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
