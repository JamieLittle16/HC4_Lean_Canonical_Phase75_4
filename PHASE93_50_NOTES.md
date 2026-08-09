# Phase 93.50 — Kernel blow-up certificate

Built on the green Phase 93.48 global restart engine and green Phase 93.49.1
linear covariance layer.

## What this phase closes

`KernelBlowupCertificate` is the exact interface a concrete DVR/kernel
rescaling must instantiate.  It contains only:

1. exact normalised gradient covariance of the transformed polynomial;
2. distinctness of the transformed marked source points;
3. the exact marked collision before transformation;
4. the positive determinant-defect update.

From this data Lean proves in one theorem:

    new marked points are distinct
    + exact collision survives
    + determinant defect strictly decreases
    + GlobalRestartProgress.

Main theorem:

    kernelBlowup_preservesCollision_and_strictlyRestarts

A JC2 terminal-target contradiction is also packaged:

    kernelBlowup_terminalTarget_impossible_of_JC2

The conformal Hessian determinant-one consequence from Phase 93.49 is
exposed as:

    conformalKernelTransform_preserves_det_one

## Scope boundary

This is not yet the concrete polynomial-family kernel blow-up construction.
The current uploaded material only exposes the *existence* of
`PolynomialFamilyCollisionSpecialFiber.lean`, not its source/API.

The next patch should discharge `KernelBlowupCertificate` using the actual
special-fibre / polynomial-family definitions.  No global restart or
collision reasoning will remain once that constructor is proved.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
