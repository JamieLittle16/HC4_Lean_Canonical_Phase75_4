import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelZeroRelativeBinaryEndpoint
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelZeroRelativeKernelPrincipalSourceLift
import Mathlib.Tactic

/-!
# Source-honest geometric assembly of the zero-relative tail

The zero-relative branch has now been exhausted finitely.  The principal
rank-two alternatives already lift to represented-source Schur geometry, while
the rank-one constant-tail alternative canonically pivots on coordinate 2 and
lifts to an actual rank-two Hessian chart on the represented state.

This file forgets only auxiliary clock bookkeeping and exposes the three honest
geometric alternatives that the final-resolution adapter must consume:

* determinant closing of the normalised 3x3 tail;
* a nonzero represented-source Schur polynomial;
* an actual represented-state rank-two Hessian chart.

No repair progress and no terminal contradiction are asserted here.
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

/-- Honest geometric alternatives left by the complete finite zero-relative
analysis. -/
inductive TopKernelThreeSchurZeroRelativeGeometricFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData)
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) : Type (u + 1)
  | determinantClosing
      (tail : ThreeSchurTangentTailKernelOpeningData S M)
      (relative_eq_zero : tail.relativeOrder = 0)
      (constantKernelOpening :
        S.toExactZeroThreeSchurClock.tailConstantMatrix
          tail.physical.index 2 ≠ 0)
      (residual_eq_zero :
        S.toExactZeroThreeSchurClock.residualDefect = 0)
      (det_ne_zero :
        S.toExactZeroThreeSchurClock.tailConstantMatrix.det ≠ 0)
  | representedSchur
      (tail : ThreeSchurTangentTailKernelOpeningData S M)
      (relative_eq_zero : tail.relativeOrder = 0)
      (constantKernelOpening :
        S.toExactZeroThreeSchurClock.tailConstantMatrix
          tail.physical.index 2 ≠ 0)
      (geometry : P.PositiveTailRepresentedSourceSchurWitness)
  | actualRankTwo
      (tail : ThreeSchurTangentTailKernelOpeningData S M)
      (relative_eq_zero : tail.relativeOrder = 0)
      (constantKernelOpening :
        S.toExactZeroThreeSchurClock.tailConstantMatrix
          tail.physical.index 2 ≠ 0)
      (geometry :
        AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented)

/-- Forget the now-exhausted binary endpoint bookkeeping while retaining the
actual source geometry that justified it. -/
theorem TopKernelThreeSchurZeroRelativeFiniteFrontier.toGeometricFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (F : P.TopKernelThreeSchurZeroRelativeFiniteFrontier S M) :
    Nonempty (P.TopKernelThreeSchurZeroRelativeGeometricFrontier S M) := by
  cases F with
  | determinantClosing tail hz hopen hres hdet =>
      exact ⟨.determinantClosing tail hz hopen hres hdet⟩
  | representedSchur tail hz hopen geometry =>
      exact ⟨.representedSchur tail hz hopen geometry⟩
  | binaryEndpoint tail hz hopen hres binary endpoint =>
      exact ⟨.actualRankTwo tail hz hopen
        binary.actualRankTwoHessianChart⟩

/-- **Zero-relative source-honest assembly.**

Every exact relative-order-zero branch reaches one of the three honest
geometric alternatives above. -/
theorem ThreeSchurTangentTailKernelOpeningData.zeroRelativeGeometricFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (D : ThreeSchurTangentTailKernelOpeningData S M)
    (hz : D.relativeOrder = 0) :
    Nonempty (P.TopKernelThreeSchurZeroRelativeGeometricFrontier S M) := by
  rcases D.zeroRelativePrincipalFrontier hz with ⟨F0⟩
  rcases F0.toSourceFrontier with ⟨F1⟩
  rcases F1.toBinaryFrontier with ⟨F2⟩
  rcases F2.toFiniteFrontier with ⟨F3⟩
  exact F3.toGeometricFrontier

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
