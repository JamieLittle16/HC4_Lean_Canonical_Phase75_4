# Phase 93.52.2 — Integral kernel blow-up proof fixes

Two local Lean proof issues are corrected.

1. `integralKernelBlowupFamily_coeff_slope_zero`

The previous proof incorrectly tried to reuse the kernel-degree-zero lemma,
which requires `d kernel = 0`.  At slope zero no such hypothesis is needed:
the rescaling exponent is `0 * d(kernel) = 0` for every monomial.

The proof now uses the general coefficientwise blow-up identity directly
and simplifies at slope zero.

2. `polynomialSectionSpecialPoint_kernelBlowupSection_kernel`

Lean requires an explicit proof that positive `slope` is nonzero before
simplifying `0 ^ slope`.

Added:

    have hslope0 : slope ≠ 0 := Nat.ne_of_gt hslope

No theorem statements or mathematical content are changed.
