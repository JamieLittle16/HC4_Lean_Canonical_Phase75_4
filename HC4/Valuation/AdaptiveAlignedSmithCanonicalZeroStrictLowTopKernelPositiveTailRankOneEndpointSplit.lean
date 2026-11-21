import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPositiveTailRankOneSourceDeparture
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPositiveTailRankOneWholeFamilyOpening
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyZeroSchurResidualClosingKernel
import Mathlib.Tactic

/-!
# Source-honest preterminal / closing split of the positive-tail rank-one clock

The generic exact rank-one clock gives the finite dichotomy

    firstOrder < defect  or  firstOrder = defect.

For the HC4 positive tail we retain the geometry instead of the old
repair-progress wrapper.

* Preterminal: the first transverse coefficient is necessarily off-diagonal.
* Exact closing: the kernel coefficient at the first/defect order is necessarily
  nonzero.

In both cases we keep represented-source Schur provenance and the exact
whole-family first-opening packet.
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

/-- Exact source-honest split of one positive-tail rank-one clock. -/
inductive PositiveTailRankOneSourceHonestEndpointSplit
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

/-- The rank-one positive tail reaches the retained preterminal/closing split
without erasing its source provenance. -/
theorem PositiveTailExplicitRankOneClockData.sourceHonestEndpointSplit
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {B : P.PositiveTailExplicitBinaryClockData S}
    (R : P.PositiveTailExplicitRankOneClockData B) :
    Nonempty (P.PositiveTailRankOneSourceHonestEndpointSplit R) := by
  let C := R.exactRankOneClock
  rcases lt_or_eq_of_le C.firstOrder_le_defect with hpre | hclose
  · have hoff : C.series.offDiag.coeff C.firstOrder ≠ 0 :=
      C.offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre
    rcases R.transverseCoeff_representedSourceGeometry
        C.firstOrder (Or.inl hoff) with ⟨G⟩
    rcases R.wholeFamilyFirstTransverseOpening with ⟨O⟩
    exact ⟨.preterminal hpre hoff G O⟩
  · have hkernel : C.series.kernel.coeff C.firstOrder ≠ 0 :=
      exactRankOneSchurClockAt_kernel_coeff_firstOrder_ne_zero_of_closing
        C hclose
    rcases R.transverseCoeff_representedSourceGeometry
        C.firstOrder (Or.inr hkernel) with ⟨G⟩
    rcases R.wholeFamilyFirstTransverseOpening with ⟨O⟩
    exact ⟨.exactClosing hclose hkernel G O⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
