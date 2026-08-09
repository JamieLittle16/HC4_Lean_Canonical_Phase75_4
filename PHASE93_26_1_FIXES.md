# Phase 93.26.1 — terminal tranche pinned-API repairs

Affected modules:

    HC4/Newton/TerminalScalarGradient.lean
    HC4/Newton/TerminalCenteredWeights.lean

No theorem statement or mathematical hypothesis changes.

## Scalar homogeneity

The failed rewrite through the function equality
`Finsupp.degree_eq_weight_one` is removed.

After unfolding weighted homogeneity, the proof now rewrites directly with

    Finsupp.weight_apply

and simplifies the constant weight `1`.  The resulting natural finite sum
is discharged by `exact_mod_cast` from the already-green integer ordinary
degree equation supplied by `HasPureQuadraticSupport`.

## Homogeneous degree zero

At exponent zero, `MvPolynomial.constantCoeff_eq` is instantiated explicitly
at `P`.

Away from exponent zero, the proof uses both orientations of the
nonzero-exponent fact (`hd` and `Ne.symm hd`) so simplification of the
coefficient of `C (...)` cannot leave a spurious `0 = d` branch.

## Gradient injectivity

The collision equality is first converted from `mvGradientMap` notation to
an explicit equality of `mvGradientAt`.  After applying matrix injectivity,
the lambda-wrapped `vecMul` target is explicitly changed to a direct matrix
equality before using the Euler/gradient identity.

## Standard terminal coordinates

Adds the reusable simp theorem

    terminalFourCoordinate_standard

showing that `terminalFourCoordinate 0 1 2 3` is the identity on `Fin 4`.

This lets the nondegenerate-Hessian row argument pass a matrix entry
directly to the actual-Hessian quadratic coefficient theorem.

No `sorry`, `admit`, `unsafe`, or new axiom is introduced.
