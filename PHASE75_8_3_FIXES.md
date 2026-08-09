# Phase 75.8.3 — Polynomial-ring congruence normalisation

This patch fixes the remaining `RankOneSchurSeriesAlignment` determinant-scaling
normalisation issue.

The left-pivot congruence is now defined directly in `Polynomial R`:

- `Cb^2 * A`
- `- 2 * Ca * Cb * B`
- `+ Ca^2 * C`

instead of first multiplying scalars in `R` and then embedding them with
`Polynomial.C`.  Consequently the determinant-scaling theorem is a pure
commutative-ring identity and closes directly by `ring`; no `Polynomial.C`
numeral/product normalisation is required.

The constant kernel proof uses `simp [pow_two]` before the already-established
scalar pivot calculation.

No theorem statements or mathematical assumptions are changed.
