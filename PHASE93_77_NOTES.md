# Phase 93.77 — Defect-retaining departure frontier

Built over green Phase 93.76.1.

The full-source audit showed that the remaining first-departure theorem
needs one piece of data which the lossless Smith frontier did not retain:
the exact Hessian determinant defect of the *transformed local family*.

This phase adds `CanonicalSmithDepartureFrontier`.

It contains the complete Phase-93.76 lossless frontier plus:

    defect : Nat
    HasPolynomialFamilyHessianDefect local.family defect

The exact defect is threaded through every local branch:

- primitive zero-Smith source: unchanged incoming defect;
- pure coefficient wall: `alignedSmithRamificationIndex * Delta`;
- no-wall primitive family:
  `alignedSmithRamificationIndex * Delta
     - 4 * (alignedSmithRamificationIndex * m)`.

The global strong induction is repeated with this stronger target, yielding

    canonicalGeometricRestart_reachesDepartureFrontier.

## Finite first positive parameter layer

The phase also defines a finite selector on the actual family support:

    familyPositiveParameterOrders
    firstPositiveParameterOrder

and proves:

- positivity;
- realisation by an actual source coefficient;
- minimality among all positive coefficient orders.

Finally every departure-ready frontier has the exact finite clock split

    no later layer
      OR first positive layer < exact Hessian defect
      OR exact Hessian defect <= first positive layer.

This is the formal preterminal-versus-closing clock required by the
first-departure theorem.

What remains is no longer a missing defect/order selector.  The remaining
geometric theorem must identify the selected first relevant layer with the
first non-one-sided Schur departure and derive its `preterminalSchurLinearSource`
equation, or construct the terminal associated-graded endpoint in the
closing branch.
