import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelLinearPowerCDGeometricFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurProjectedSourceLift
import Mathlib.Tactic

/-!
# Fully source-honest C/D frontier for the top-kernel linear-power branch

The assembly-facing C/D frontier had one intentionally provisional constructor:
`projectedRankTwo`, whose witness lived in the cleared 1+3 quotient.
The projected source-lift now turns that constructor into an honest exact-active
Hessian chart of the represented blocker state.

The old `actualRankTwo` constructor is also an exact-active chart through the
existing direct embedding.  Hence the complete pre-relative C/D analysis now
has only two source-honest outputs:

* an honest exact-active represented-state Hessian chart; or
* the already-complete exact relative geometric frontier.

No quotient-only rank label remains in the public C/D seam.
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

/-- Source-honest C/D assembly frontier after eliminating the last
quotient-only projected-rank-two constructor. -/
inductive TopKernelLinearPowerCDSourceFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | exactActive
      (geometry :
        AdaptiveAlignedSmithCanonicalExactActiveFourBlock
          T.terminal.blocker.presented)
  | relative
      (layer : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak)
      (clock : P.TopKernelThreeSchurClockData)
      (tangent : ThreeSchurTangentAtFirstBreak clock layer)
      (geometry : P.TopKernelThreeSchurRelativeGeometricFrontier clock layer)

/-- **C/D is now fully source-honest.**

Every top-kernel linear-power packet reaches either a genuine exact-active
represented-state Hessian chart or the already-finished exact relative
geometric frontier. -/
theorem topKernelLinearPowerCDSourceFrontier_nonempty
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty P.TopKernelLinearPowerCDSourceFrontier := by
  rcases P.topKernelLinearPowerCDGeometricFrontier_nonempty with ⟨F⟩
  cases F with
  | actualRankTwo A =>
      exact ⟨.exactActive
        (AdaptiveAlignedSmithCanonicalExactActiveFourBlock.ofDirect A)⟩
  | projectedRankTwo M S G =>
      rcases P.projectedRankTwo_exactActiveFourBlock S M G with ⟨A⟩
      exact ⟨.exactActive A⟩
  | relative M S R G =>
      exact ⟨.relative M S R G⟩

/-- Canonical Type-valued source-honest C/D frontier. -/
noncomputable def topKernelLinearPowerCDSourceFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    P.TopKernelLinearPowerCDSourceFrontier :=
  Classical.choice P.topKernelLinearPowerCDSourceFrontier_nonempty

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
