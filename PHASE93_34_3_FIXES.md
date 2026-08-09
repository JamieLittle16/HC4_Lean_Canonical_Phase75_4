# Phase 93.34.3 — stop extensionality at the matrix entries

Affected module:

    HC4/Newton/TerminalOneZeroHessianFactor.lean

The Phase 93.34.2 patch was applied correctly.  It removed the unwanted
two-zero `standardTwoZeroA/C` simplifications.

The remaining log showed goals of the form

    coeff m (pderiv 2 (pderiv 1 F)) = 0

rather than the intended polynomial equality

    pderiv 2 (pderiv 1 F) = 0.

This happened because the generic tactic

    ext i j

continued extensionality through the matrix entry type
`MvPolynomial (Fin 4) K`, introducing an additional arbitrary monomial
coefficient.

The repair stops extensionality exactly at the matrix level:

    apply Matrix.ext
    intro i j

The 16 entries are then polynomial equalities.  After the coordinate split,
the sparse identities

    hz.1
    hz.2.1
    hz.2.2

and mixed-partial commutation close the zero row/column directly.

No theorem statement, hypothesis, or mathematical argument changes.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
