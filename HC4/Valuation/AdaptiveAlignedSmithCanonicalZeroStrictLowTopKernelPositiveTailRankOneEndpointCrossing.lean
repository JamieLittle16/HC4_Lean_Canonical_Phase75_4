import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPositiveTailRankOneEndpointSplit
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurProjectiveWedgeConstancy
import Mathlib.Tactic

/-!
# Source-point crossings for the positive-tail rank-one endpoint split

The positive-tail rank-one clock has already been reduced source-honestly to two
exact timing alternatives:

* preterminal: the first transverse off-diagonal coefficient is a nonzero
  four-variable source polynomial;
* exact closing: the first transverse kernel coefficient is a nonzero
  four-variable source polynomial.

A nonzero polynomial over the present characteristic-zero field is nonzero at
some source point.  This file retains such a point without identifying the
Schur coefficient with a Hessian potential and without introducing repair
progress.
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

/-- Exact preterminal/closing endpoint data together with an actual source
point at which the first transverse source polynomial is nonzero. -/
inductive PositiveTailRankOneSourceHonestEndpointCrossing
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (R : P.PositiveTailExplicitRankOneClockData B) : Type (u + 1)
  | preterminal
      (firstOrder_lt :
        R.exactRankOneClock.firstOrder < R.exactRankOneClock.defect)
      (offDiag_ne :
        R.exactRankOneClock.series.offDiag.coeff
          R.exactRankOneClock.firstOrder ≠ 0)
      (sourceGeometry :
        P.PositiveTailRankOneTransverseRepresentedSourceGeometry B)
      (wholeOpening :
        P.PositiveTailRankOneWholeFamilyFirstTransverseOpening R)
      (point : Fin 4 → K)
      (point_ne :
        MvPolynomial.eval point
          (R.exactRankOneClock.series.offDiag.coeff
            R.exactRankOneClock.firstOrder) ≠ 0)
  | exactClosing
      (firstOrder_eq :
        R.exactRankOneClock.firstOrder = R.exactRankOneClock.defect)
      (kernel_ne :
        R.exactRankOneClock.series.kernel.coeff
          R.exactRankOneClock.firstOrder ≠ 0)
      (sourceGeometry :
        P.PositiveTailRankOneTransverseRepresentedSourceGeometry B)
      (wholeOpening :
        P.PositiveTailRankOneWholeFamilyFirstTransverseOpening R)
      (point : Fin 4 → K)
      (point_ne :
        MvPolynomial.eval point
          (R.exactRankOneClock.series.kernel.coeff
            R.exactRankOneClock.firstOrder) ≠ 0)

/-- Every source-honest positive-tail rank-one endpoint has an actual
source-point crossing of its first transverse polynomial. -/
theorem PositiveTailExplicitRankOneClockData.sourceHonestEndpointCrossing
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (R : P.PositiveTailExplicitRankOneClockData B) :
    Nonempty (P.PositiveTailRankOneSourceHonestEndpointCrossing R) := by
  rcases R.sourceHonestEndpointSplit with ⟨E⟩
  cases E with
  | preterminal hpre hoff geometry opening =>
      rcases exists_source_eval_ne_zero_of_ne_zero
          (R.exactRankOneClock.series.offDiag.coeff
            R.exactRankOneClock.firstOrder)
          hoff with ⟨point, hpoint⟩
      exact ⟨.preterminal hpre hoff geometry opening point hpoint⟩
  | exactClosing hclose hkernel geometry opening =>
      rcases exists_source_eval_ne_zero_of_ne_zero
          (R.exactRankOneClock.series.kernel.coeff
            R.exactRankOneClock.firstOrder)
          hkernel with ⟨point, hpoint⟩
      exact ⟨.exactClosing hclose hkernel geometry opening point hpoint⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
