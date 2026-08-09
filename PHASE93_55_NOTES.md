# Phase 93.55 — Concrete integral kernel restart

Built on green Phase 93.54.2.

## Positive slope

The theorem

    integralKernelBlowup_toPolynomialFamilyKernelRestartCertificate

constructs the Phase 93.51 restart certificate directly from:
- coefficient divisibility for the explicit Phase 93.52 blow-up;
- the original exact family collision;
- distinct reductions of the transformed sections;
- the positive defect-drop arithmetic certificate.

The transformed family-collision field is no longer assumed: it is proved
by the green Phase 93.54 derivative covariance theorem.

The end-to-end theorem

    integralKernelBlowup_preservesSpecialCollision_and_strictlyRestarts

returns:
- distinct special points;
- exact special-fibre gradient collision;
- strict defect decrease;
- GlobalRestartProgress.

A pointed origin form and the terminal JC2 contradiction are also provided.

## Zero slope

`integralKernelBlowupFamily_zero_eq` proves the explicit reconstructed
blow-up family is literally the original family at slope zero.

Together with the already-green `kernelBlowupSection_zero`:

    integralKernelBlowup_zero_is_identity

shows that zero slope is not a restart at all. It must be classified in the
current special fibre, exactly as required by the audited restart blueprint.

## Remaining substantive global step

The positive-slope logical branch is now fully assembled. The remaining
geometric extraction theorem must show, for an arbitrary nonterminal restart
datum, either:
- a positive slope with the coefficient divisibility, special-point
  distinctness, and defect update used here; or
- zero slope, in which case the current special fibre enters the already
  formalised Smith/local classifier.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
