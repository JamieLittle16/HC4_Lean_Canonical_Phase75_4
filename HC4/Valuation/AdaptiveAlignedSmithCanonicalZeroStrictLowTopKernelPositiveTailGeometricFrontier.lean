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

/-- Timing-preserving refinement of the positive-tail geometric frontier.

The older assembly interface deliberately collapsed the exact rank-one timing
split into a common source-point geometry.  For terminal extraction that loses
one crucial fact: in the exact-closing branch the first transverse order is
literally the determinant defect, and the same packet retains an honest
whole-family first opening.  Keep that branch explicit here while leaving the
already-useful source-geometry frontier unchanged. -/
inductive TopKernelThreeSchurPositiveTailTimingFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) : Type (u + 1)
  | representedThreeByThree
      (geometry : P.PositiveTailRepresentedSourceThreeByThreePointGeometry)
  | rankOnePreterminal
      (binary : P.PositiveTailExplicitBinaryClockData S)
      (rankOne : P.PositiveTailExplicitRankOneClockData binary)
      (geometry : P.PositiveTailRankOnePreterminalSourcePointGeometry rankOne)
  | rankOneExactClosing
      (binary : P.PositiveTailExplicitBinaryClockData S)
      (rankOne : P.PositiveTailExplicitRankOneClockData binary)
      (geometry : P.PositiveTailRankOneClosingSourcePointGeometry rankOne)

/-- Recover the timing information which is still present in every constructor
of the source-point frontier.  In particular the exact-closing constructor
retains firstOrder = defect and the physical whole-family opening. -/
theorem TopKernelThreeSchurPositiveTailGeometricFrontier.toTimingFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (F : P.TopKernelThreeSchurPositiveTailGeometricFrontier S) :
    Nonempty (P.TopKernelThreeSchurPositiveTailTimingFrontier S) := by
  cases F with
  | representedThreeByThree G =>
      exact ⟨.representedThreeByThree G⟩
  | rankOneSourcePoint binary rankOne G =>
      cases G with
      | preterminal E =>
          exact ⟨.rankOnePreterminal binary rankOne E⟩
      | exactClosing E =>
          exact ⟨.rankOneExactClosing binary rankOne E⟩

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

/-- Assembly-facing positive-relative timing frontier.  This is the preferred
interface for the remaining terminal adapter because it does not erase exact
closing before the associated-graded fibre has been constructed. -/
theorem ThreeSchurTangentTailKernelOpeningData.positiveTailTimingFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (D : ThreeSchurTangentTailKernelOpeningData S M)
    (hpos : 0 < D.relativeOrder) :
    Nonempty (P.TopKernelThreeSchurPositiveTailTimingFrontier S) := by
  rcases D.positiveTailGeometricFrontier hpos with ⟨F⟩
  exact F.toTimingFrontier

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
