# Phase 93.27.1 — planar interface and nonnegative-weight repairs

Affected modules:

    HC4/PlanarJC2Interface.lean
    HC4/Newton/TerminalNonnegativeWeights.lean

## Planar JC2 interface

`MvPolynomial.pderiv` was unavailable because the file imported only the
matrix determinant layer.  The module now imports

    Mathlib.RingTheory.MvPolynomial.EulerIdentity

which is the same derivative-capable MvPolynomial layer already used by the
green Newton collision modules.

`PlanarPolynomialMap` is also now declared with the explicit

    [CommSemiring K]

constraint required while elaborating `MvPolynomial (Fin 2) K`.

The later definitions are still used under `[Field K]`, so this introduces
no new mathematical hypothesis in the HC4 application.

The compiler's temporary `declaration uses 'sorry'` warning was fallout
from the failed type abbreviation elaboration; the source contains no
`sorry`.

## Nonnegative terminal weights

The proof that a non-scalar weight is nontrivial no longer relies on
`push_neg`.

Assuming no coordinate is nonzero, the proof explicitly derives

    lambda i = 0

for every `i`, making the weight scalar with common value zero and
contradicting `IsNonScalarIntegralWeight`.

No theorem statement changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
