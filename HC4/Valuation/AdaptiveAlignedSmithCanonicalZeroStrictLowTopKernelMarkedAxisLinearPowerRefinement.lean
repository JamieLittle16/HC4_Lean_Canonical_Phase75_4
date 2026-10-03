import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisLinearPowerSplit
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelLinearPowerFirstBreak
import Mathlib.Tactic

/-!
# E1: nonzero refinement of the marked-axis linear-power split

The support split for a top-kernel linear-power residual deliberately allowed
the marked-axis first-contact fibre to be zero.  That possibility must be
separated before the E-stage treats the fibre as a genuine support carrier.

There are exactly three honest outcomes:

* the marked slice is zero; in this case we retain the already-green honest
  ordinary reverse-Rees first-break rank-two package instead of pretending a
  zero polynomial is a terminal face;
* the stored top kernel is the marked coordinate, so the marked fibre is
  literally the whole nonzero top face;
* the marked fibre is nonzero and is supported with two distinct coordinate
  exponents identically zero.

This is still an E1 support/refinement theorem.  No rank-two packet is treated
as a contradiction and no terminal endpoint is manufactured.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- E1 refinement of the actual marked-axis slice in the top-kernel
linear-power residual. -/
inductive TopKernelMarkedAxisLinearPowerRefinement
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | emptySlice
      (fibre_eq_zero :
        polynomialFamilySpecialFiber
            T.topKernelMarkedAxisFirstContactFamily = 0)
      (firstBreak :
        let B := kernelLastFamilyHessianFourBlock
          T.topKernelReverseReesFamily kernelCoordinate
        let hrow := T.topKernelLastBlock_kernelRow_ne_zero kernelCoordinate
        let j := firstFourBlockKernelRowBreakOrder B hrow
        RankOneSpecialFiberFirstBreakOutcome B j)
  | wholeTopFace
      (kernel_eq_zero : kernelCoordinate = (0 : Fin 4))
      (fibre_eq_topFace :
        polynomialFamilySpecialFiber
            T.topKernelMarkedAxisFirstContactFamily =
          T.topFace.face)
  | nonzeroBinarySlice
      (kernel_ne_zero : kernelCoordinate ≠ (0 : Fin 4))
      (fibre_ne_zero :
        polynomialFamilySpecialFiber
            T.topKernelMarkedAxisFirstContactFamily ≠ 0)
      (kernel_derivative_zero :
        MvPolynomial.pderiv kernelCoordinate
            (polynomialFamilySpecialFiber
              T.topKernelMarkedAxisFirstContactFamily) = 0)
      (support_two_zero :
        ∀ d ∈ (polynomialFamilySpecialFiber
              T.topKernelMarkedAxisFirstContactFamily).support,
          d (0 : Fin 4) = 0 ∧ d kernelCoordinate = 0)

/-- **Exact nonzero-aware E1 split.**

A zero marked slice is routed back to the already-green source-honest
first-break package.  Otherwise the previous support split sharpens to either
the entire nonzero top face or a genuinely nonzero binary-supported slice. -/
theorem markedAxisLinearPowerRefinement
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty P.TopKernelMarkedAxisLinearPowerRefinement := by
  by_cases hfibre :
      polynomialFamilySpecialFiber
          T.topKernelMarkedAxisFirstContactFamily = 0
  · exact ⟨.emptySlice hfibre P.firstBreakRankTwoOutcome⟩
  · rcases P.markedAxisLinearPowerSupportSplit with ⟨S⟩
    cases S with
    | markedKernel hk heq =>
        exact ⟨.wholeTopFace hk heq⟩
    | binarySupported hk hderiv hsupp =>
        exact ⟨.nonzeroBinarySlice hk hfibre hderiv hsupp⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
