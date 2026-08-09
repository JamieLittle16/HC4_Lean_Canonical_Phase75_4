# Phase 75.9.1 — Canonical Smith-Rees compile repair

This patch repairs the first compile of `CanonicalSmithReesSpecialFiber.lean`
without changing the mathematical interfaces introduced in Phase 75.9.

Changes:

- removes invalid explicit `(K := K)` arguments from exponent-only lemmas whose
  statements do not depend on the coefficient field;
- proves the `(2,2)` raw-exponent / symmetric-separator identity directly from
  the already-green Smith definitions and `smithExtremeSeparator_one_one`;
- makes the `X^4` divisibility factorisation explicit rather than relying on
  ring normalisation across natural-number exponents;
- unfolds `canonicalSmithReesFamily` before applying the general coefficient
  theorem in the exact-special-fibre proof.

No theorem statements or assumptions are weakened. No `sorry`, `admit`, or
`unsafe` is introduced.
