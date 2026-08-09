# Phase 75.4.8 — First Schur equality-orientation fix

This is a one-line corrective patch for `FirstSchurDepartureBridge.lean`.

In the nonzero source-monomial branch, `MvPolynomial.coeff_C` produces the guard
`0 = d`, while the branch hypothesis has type `d ≠ 0`.  The simplifier therefore
needs the symmetric disequality `Ne.symm hd : 0 ≠ d`.

No definitions, theorem statements, or mathematical interfaces are changed.
