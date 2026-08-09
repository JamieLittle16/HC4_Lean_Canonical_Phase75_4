# Phase 91.3 — transverse support rigidity

## New module

    HC4/Newton/TransverseSupportRigidity.lean

This phase corrects an important potential shortcut before formalising it.

Ordinary homogeneity together with `D²F = 0` does not imply `DF = 0`
(e.g. `F=x*y`, `D=∂x`).  The HC4 argument instead uses positive
homogeneity in the two transverse variables plus independence of those
same variables.

The new predicates are:

    HasPositiveTransverseSupport
    HasExactTransverseDegree
    IsTransverselyIndependent

Lean proves that a polynomial with strictly positive transverse degree in
every nonzero monomial cannot simultaneously be independent of both
transverse variables unless it is zero.

The directional-derivative endpoint is:

    binaryDirectionalDeriv_eq_zero_of_exactPositiveDegree_of_independent

Thus the remaining task for the Hessian-integrability layer is precise:
derive transverse independence of `D F` from the two Hessian-row kernel
equations (in characteristic zero), while homogeneity supplies its positive
transverse degree.

No previous theorem statement is changed.
No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
