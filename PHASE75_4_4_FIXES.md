# Phase 75.4.4 — Actual parameter layer map fix

This corrective patch replaces the hand-written `MvPolynomial.sum` reconstruction
of `familyParameterLayer` with coefficient-wise `AddMonoidAlgebra.map`.

The coefficient lemma is then an immediate application of
`MvPolynomial.coeff_addMonoidAlgebraMap`; this avoids the brittle support/sum
simplification that failed in 75.4.2.

No mathematical theorem statement downstream is changed.
