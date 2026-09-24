import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPositiveTailSourceHonestFrontier
import Mathlib.Tactic

/-!
# Exact timing split for the source-honest positive relative tail

The source-honest positive-tail frontier has already removed every auxiliary
normalisation that does not matter to the final endpoint.  Its rank-one branch
retains the exact oriented rank-one clock together with the exact whole-family
first transverse opening.

For an exact rank-one Schur clock the first transverse order is at most the
determinant-closing order.  Hence there are only two timing possibilities:

* preterminal: the first transverse order is strictly below the defect;
* exact closing: the first transverse order equals the defect.

This file records that split without converting either branch to repair
progress.  The represented-source Schur alternative is retained verbatim.
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

/-- Source-honest positive-tail data with the final rank-one timing ambiguity
removed.

The two rank-one constructors retain the same whole-family first-opening
certificate; the only extra datum is whether the exact clock opens strictly
before determinant closure or exactly at closure. -/
inductive TopKernelThreeSchurPositiveTailTimedFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) : Type (u + 1)
  | representedSchur
      (geometry : P.PositiveTailRepresentedSourceSchurWitness)
  | rankOnePreterminal
      (binary : P.PositiveTailExplicitBinaryClockData S)
      (rankOne : P.PositiveTailExplicitRankOneClockData binary)
      (opening : P.PositiveTailRankOneWholeFamilyFirstTransverseOpening rankOne)
      (firstOrder_lt_defect :
        rankOne.clock.firstOrder < rankOne.clock.defect)
  | rankOneExactClosing
      (binary : P.PositiveTailExplicitBinaryClockData S)
      (rankOne : P.PositiveTailExplicitRankOneClockData binary)
      (opening : P.PositiveTailRankOneWholeFamilyFirstTransverseOpening rankOne)
      (firstOrder_eq_defect :
        rankOne.clock.firstOrder = rankOne.clock.defect)

/-- The source-honest frontier has no remaining timing branch beyond
preterminal versus exact determinant closing. -/
theorem TopKernelThreeSchurPositiveTailSourceHonestFrontier.toTimedFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (F : P.TopKernelThreeSchurPositiveTailSourceHonestFrontier S) :
    Nonempty (P.TopKernelThreeSchurPositiveTailTimedFrontier S) := by
  cases F with
  | representedSchur geometry =>
      exact ⟨.representedSchur geometry⟩
  | rankOneWholeFamilyOpening binary rankOne opening =>
      rcases lt_or_eq_of_le rankOne.clock.firstOrder_le_defect with hpre | hclose
      · exact ⟨.rankOnePreterminal binary rankOne opening hpre⟩
      · exact ⟨.rankOneExactClosing binary rankOne opening hclose⟩

/-- Assembly-facing timed positive-relative theorem. -/
theorem ThreeSchurTangentTailKernelOpeningData.positiveTailTimedFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (D : ThreeSchurTangentTailKernelOpeningData S M)
    (hpos : 0 < D.relativeOrder) :
    Nonempty (P.TopKernelThreeSchurPositiveTailTimedFrontier S) := by
  rcases D.positiveTailSourceHonestFrontier hpos with ⟨F⟩
  exact F.toTimedFrontier

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
