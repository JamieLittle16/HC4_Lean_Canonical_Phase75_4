# Phase 75.8.2 — Schur alignment ring-normalisation fix

This patch repairs the two remaining algebra-normalisation failures in
`HC4.Newton.RankOneSchurSeriesAlignment`.

1. `alignLeft.kernel_coeff_zero` now factors the constant kernel coefficient as
   `a * (a*c - b*b)` and uses the left-pivot determinant-zero relation directly.
   This avoids a brittle rewrite into a differently-associated monomial.

2. `alignLeft_determinant` explicitly normalises the constant-polynomial map via
   `Polynomial.C_mul` and `Polynomial.C_eq_natCast` before invoking `ring`.
   This exposes identities such as `C (a*b) = C a * C b`, which the ring tactic
   otherwise treats as unrelated atoms.

No theorem statements or mathematical assumptions are changed.
No `sorry`, `admit`, or `unsafe` is introduced.
