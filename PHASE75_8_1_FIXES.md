# Phase 75.8.1 — CommRing Schur / ring-level pivot fix

Phase 75.8 crossed two older field-specialised APIs while its actual Schur
series lives over polynomial coefficient rings:

1. `BinarySchurBlock.detCore` inherited `[Field R]`, but the general four-block
   identity is used with `R = Polynomial (...)`.
2. `BinarySchurBlock.LeftPivot` / `RightAxisPivot` also inherited a field
   assumption, while the constant Schur block at this stage has coefficients
   in `MvPolynomial (Fin 4) K`.

This patch fixes the abstraction boundary rather than adding impossible field
instances:

* `GeneralFourBlock.schurDetCore` is the raw expression
  `schurA * schurC - schurB * schurB` over any `CommRing`.
* the general identity
  `schurDetCore = activeDet * determinantCore` remains a pure ring theorem.
* `BinarySchurPolynomialSeries.LeftPivot` and `RightAxisPivot` are ring-level
  predicates with exactly the algebraic data needed by the constant
  congruences; no division or field structure is used.
* the alignment and frontier constructors now use those ring-level pivots.
* scalar/field-specific `BinarySchurBlock` geometry is left untouched for the
  older modules that genuinely need it.

No `sorry`, `admit`, or `unsafe` is introduced.
