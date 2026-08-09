# Phase 93.57 — Exact kernel defect drop

Built over the green Phase 93.56.2 tree.

## Closed in this phase

1. Coefficientwise inflation formula:
   `coeff_kernelInflateHom`.

2. Injectivity of the kernel inflation homomorphism:
   `kernelInflateHom_injective`.

3. The determinant factorisation itself forces:
   `2 * slope <= Delta`.
   No half-defect bound is assumed.

4. Exact target determinant defect:
   `integralKernelBlowup_hasHessianDefect_sub`

       det Hess(Ptilde) = tau^(Delta - 2*slope).

5. Automatic construction of:
   `HasPositiveKernelDefectDrop`.

6. End-to-end theorem:
   `integralKernelBlowup_exactDefect_and_strictRestart`

   simultaneously returns:
   - exact target Hessian defect;
   - distinct special points;
   - exact special-fibre gradient collision;
   - strict numerical defect descent;
   - `GlobalRestartProgress`.

## Remaining substantive theorem

The positive-slope branch is now algebraically complete. The remaining
global geometric extraction must prove that any nonterminal HC4 collision
datum supplies either:
- a positive slope with the coefficient divisibility and special-point
  distinctness consumed here; or
- zero slope, which stays on the current fibre and enters the already-green
  Smith/local classifier.

No `sorry`, `admit`, `axiom`, or `unsafe` declarations are introduced.
