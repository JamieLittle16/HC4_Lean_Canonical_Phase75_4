# Phase 93.51 — Polynomial-family kernel restart

Built against the exact green Phase 93.50 concrete-kernel checkpoint.

## Existing API used directly

`PolynomialFamilyCollisionSpecialFiber.lean` already proves:

    HasPolynomialFamilyExactGradientCollision P a b
      ->
    HasExactGradientCollision
      (polynomialFamilySpecialFiber P)
      (polynomialSectionSpecialPoint a)
      (polynomialSectionSpecialPoint b).

Phase 93.51 joins this exact theorem to the green global defect/restart
machinery.

## New generic certificate

`PolynomialFamilyKernelRestartCertificate` requires only:

1. an exact family gradient collision;
2. distinct special points;
3. a positive kernel defect drop.

Then

`polynomialFamilyKernelRestart_preservesCollision_and_strictlyRestarts`

returns:

- distinct special-fibre marked points;
- exact special-fibre gradient collision;
- strict determinant-defect drop;
- `GlobalRestartProgress`.

## Pointed normalised certificate

`PointedPolynomialFamilyKernelRestartCertificate` packages the important
normalisation:

    a(0) = 0,
    b(0) = r,
    r != 0.

Then

`pointedPolynomialFamilyKernelRestart_zeroCollision_and_strictlyRestarts`

returns the exact collision

    grad(P_0)(0) = grad(P_0)(r)

together with strict global restart progress.

Under JC2, a certified terminal special fibre is immediately contradictory:

`pointedPolynomialFamilyKernelRestart_terminalSpecialFiber_impossible_of_JC2`.

## Remaining concrete step

The remaining kernel-blow-up construction must build an actual polynomial
family `P : MvPolynomial (Fin 4) (Polynomial K)` and moving sections whose
family collision is exact, and prove the determinant-defect update.  Once
those are constructed, no further specialisation/restart logic is needed.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
