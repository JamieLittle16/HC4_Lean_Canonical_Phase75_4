import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPositiveTailRankOneWholeFamilyOpening
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelPositiveTailRepresentedSourceSchur
import Mathlib.Tactic

/-!
# Source-honest assembly of the positive relative three-Schur tail

The positive-relative tail has already been reduced to three finite alternatives:

* an active rank-two constant block;
* an exact binary determinant-closing clock; or
* an oriented exact rank-one clock.

The first two alternatives now lift to a branch-independent nonzero Schur
polynomial on the represented determinant-one source.  The rank-one alternative
retains its exact whole-family first transverse opening, including the physical
parameter order.

This file assembles those facts into the interface consumed by the final
positive-tail endpoint step.  No repair progress is introduced.
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

/-- Honest positive-tail inputs left after all auxiliary Schur normalisations
have been discharged.

The finite rank-two and binary-closing alternatives retain only represented
source Schur geometry.  The rank-one alternative retains the exact first
whole-family opening because C4/C5 still need its physical parameter order. -/
inductive TopKernelThreeSchurPositiveTailSourceHonestFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (S : P.TopKernelThreeSchurClockData) : Type (u + 1)
  | representedSchur
      (geometry : P.PositiveTailRepresentedSourceSchurWitness)
  | rankOneWholeFamilyOpening
      (binary : P.PositiveTailExplicitBinaryClockData S)
      (rankOne : P.PositiveTailExplicitRankOneClockData binary)
      (opening : P.PositiveTailRankOneWholeFamilyFirstTransverseOpening rankOne)

/-- Every fully filtered positive-tail branch reaches the source-honest
frontier.  This is the assembly form of C1--C3. -/
theorem TopKernelThreeSchurPositiveTailRankOneFrontier.toSourceHonestFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (F : P.TopKernelThreeSchurPositiveTailRankOneFrontier S) :
    Nonempty (P.TopKernelThreeSchurPositiveTailSourceHonestFrontier S) := by
  cases F with
  | activeRankTwo hres h01 =>
      exact ⟨.representedSchur
        (S.activeRankTwo_representedSourceSchurWitness h01)⟩
  | binaryDeterminantClosing hres B hzero hdet =>
      exact ⟨.representedSchur B.representedSourceSchurWitness⟩
  | rankOneClock hres B R =>
      rcases R.wholeFamilyFirstTransverseOpening with ⟨O⟩
      exact ⟨.rankOneWholeFamilyOpening B R O⟩

/-- Assembly-facing positive-relative tail theorem: once the exact relative
order is positive, the branch reaches honest represented-source Schur geometry
or an exact whole-family first transverse opening. -/
theorem ThreeSchurTangentTailKernelOpeningData.positiveTailSourceHonestFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (D : ThreeSchurTangentTailKernelOpeningData S M)
    (hpos : 0 < D.relativeOrder) :
    Nonempty (P.TopKernelThreeSchurPositiveTailSourceHonestFrontier S) := by
  rcases D.positiveTailRankOneFrontier hpos with ⟨F⟩
  exact F.toSourceHonestFrontier

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
