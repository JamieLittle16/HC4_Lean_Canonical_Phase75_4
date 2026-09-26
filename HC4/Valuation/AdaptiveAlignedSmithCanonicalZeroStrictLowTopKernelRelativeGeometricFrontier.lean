import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurRelativeTailFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPositiveTailGeometricFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelZeroRelativeGeometricFrontier
import Mathlib.Tactic

/-!
# Unified geometric frontier for the exact relative-order split

The exact relative-order split `r = J - q` is now source-honest on both
sides.  This file joins the two branches without weakening either payload:

* `r > 0` retains the complete positive-tail source-point geometry;
* `r = 0` retains the complete zero-relative source geometry.

This is the single top-kernel geometric interface that the final terminal
resolution step must consume.  No repair progress or contradiction is added.
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

/-- Complete source-honest geometry after the exact relative-order split. -/
inductive TopKernelThreeSchurRelativeGeometricFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) : Type (u + 1)
  | zeroRelative
      (tail : ThreeSchurTangentTailKernelOpeningData S M)
      (relative_eq_zero : tail.relativeOrder = 0)
      (geometry : P.TopKernelThreeSchurZeroRelativeGeometricFrontier S M)
  | positiveRelative
      (tail : ThreeSchurTangentTailKernelOpeningData S M)
      (relative_pos : 0 < tail.relativeOrder)
      (geometry : P.TopKernelThreeSchurPositiveTailGeometricFrontier S)

/-- Upgrade the exact arithmetic split to the complete source-honest geometric
split. -/
theorem TopKernelThreeSchurRelativeTailFrontier.toGeometricFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (F : P.TopKernelThreeSchurRelativeTailFrontier S M) :
    Nonempty (P.TopKernelThreeSchurRelativeGeometricFrontier S M) := by
  cases F with
  | zeroRelative tail hz hcommon hopen =>
      rcases tail.zeroRelativeGeometricFrontier hz with ⟨G⟩
      exact ⟨.zeroRelative tail hz G⟩
  | positiveRelative tail hpos frontier =>
      rcases tail.positiveTailGeometricFrontier hpos with ⟨G⟩
      exact ⟨.positiveRelative tail hpos G⟩

/-- **Unified top-kernel geometric endpoint.**

Every tangent first-break packet reaches one source-honest geometric frontier,
with the exact relative-order branch retained. -/
theorem ThreeSchurTangentAtFirstBreak.relativeGeometricFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (R : ThreeSchurTangentAtFirstBreak S M) :
    Nonempty (P.TopKernelThreeSchurRelativeGeometricFrontier S M) := by
  rcases R.relativeTailFrontier with ⟨F⟩
  exact F.toGeometricFrontier

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
