import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPositiveTailSourceHonestFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPositiveTailRankOneGeometricEndpoint
import Mathlib.Tactic

/-!
# Finite source-point geometric frontier for the positive relative tail

The positive relative tail is source-honest before this file starts.

* The finite active-rank-two and binary-determinant-closing alternatives yield
  an actual nonzero evaluated 3x3 Hessian minor on the represented source.
* The rank-one alternative yields either a preterminal evaluated binary Schur
  block with nonzero determinant `-b^2`, or an exact-closing nonzero kernel
  crossing.

This file only assembles these facts.  It does not identify a Schur polynomial
with a Hessian potential, does not claim repair progress, and does not
manufacture a terminal associated-graded fibre.
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

/-- Complete finite source-point geometry of the positive relative tail. -/
inductive TopKernelThreeSchurPositiveTailGeometricFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) : Type (u + 1)
  | representedThreeByThree
      (geometry : P.PositiveTailRepresentedSourceThreeByThreePointGeometry)
  | rankOneSourcePoint
      (binary : P.PositiveTailExplicitBinaryClockData S)
      (rankOne : P.PositiveTailExplicitRankOneClockData binary)
      (geometry : P.PositiveTailRankOneSourcePointGeometricEndpoint rankOne)

/-- Every source-honest positive-tail packet reaches literal source-point
geometry. -/
theorem TopKernelThreeSchurPositiveTailSourceHonestFrontier.toGeometricFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (F : P.TopKernelThreeSchurPositiveTailSourceHonestFrontier S) :
    Nonempty (P.TopKernelThreeSchurPositiveTailGeometricFrontier S) := by
  cases F with
  | representedSchur geometry =>
      rcases geometry.exists_threeByThreePointGeometry with ⟨G⟩
      exact ⟨.representedThreeByThree G⟩
  | rankOneEndpointSplit binary rankOne split =>
      rcases split.toSourcePointGeometricEndpoint with ⟨G⟩
      exact ⟨.rankOneSourcePoint binary rankOne G⟩

/-- Assembly-facing positive-relative geometric frontier. -/
theorem ThreeSchurTangentTailKernelOpeningData.positiveTailGeometricFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (D : ThreeSchurTangentTailKernelOpeningData S M)
    (hpos : 0 < D.relativeOrder) :
    Nonempty (P.TopKernelThreeSchurPositiveTailGeometricFrontier S) := by
  rcases D.positiveTailSourceHonestFrontier hpos with ⟨F⟩
  exact F.toGeometricFrontier

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
