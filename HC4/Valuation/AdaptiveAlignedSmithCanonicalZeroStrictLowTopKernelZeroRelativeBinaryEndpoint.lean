import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelZeroRelativeBinaryProvenance
import HC4.Valuation.AdaptiveAlignedSmithCanonicalStationaryPlanarCoreFinalAssemblyZeroSchurResidualClosingKernel
import Mathlib.Tactic

/-!
# Finite binary endpoint split for the zero-relative tail

After D3 the only unresolved zero-relative rank-one branch carries a canonical
coordinate-2 exact binary zero-Schur clock.  There are no further geometric
choices:

* zero binary residual defect gives a nondegenerate constant binary block;
* positive binary residual defect gives a literal left or right rank-one pivot;
* each exact rank-one clock opens either strictly before determinant closure,
  where its first transverse coefficient is off-diagonal, or exactly at
  closure, where its kernel coefficient is nonzero.

This file records that finite exhaustion without introducing repair progress
or a new staircase.
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

/-- Complete finite endpoint split of one zero-relative explicit binary clock. -/
inductive ZeroRelativeExplicitBinaryEndpointSplit
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (B : P.ZeroRelativeExplicitBinaryClockData S) : Type (u + 1)
  | determinantClosing
      (residual_eq_zero : B.clock.residualDefect = 0)
      (det_ne_zero :
        B.clock.tailSeries.active.coeff 0 *
              B.clock.tailSeries.kernel.coeff 0 -
            B.clock.tailSeries.offDiag.coeff 0 *
              B.clock.tailSeries.offDiag.coeff 0 ≠ 0)
  | leftPreterminal
      (residual_pos : 0 < B.clock.residualDefect)
      (pivot : B.clock.tailSeries.LeftPivot)
      (firstOrder_lt :
        (B.clock.toRankOneClockLeft residual_pos pivot).firstOrder <
          (B.clock.toRankOneClockLeft residual_pos pivot).defect)
      (offDiag_ne :
        (B.clock.toRankOneClockLeft residual_pos pivot).series.offDiag.coeff
          (B.clock.toRankOneClockLeft residual_pos pivot).firstOrder ≠ 0)
  | leftExactClosing
      (residual_pos : 0 < B.clock.residualDefect)
      (pivot : B.clock.tailSeries.LeftPivot)
      (firstOrder_eq :
        (B.clock.toRankOneClockLeft residual_pos pivot).firstOrder =
          (B.clock.toRankOneClockLeft residual_pos pivot).defect)
      (kernel_ne :
        (B.clock.toRankOneClockLeft residual_pos pivot).series.kernel.coeff
          (B.clock.toRankOneClockLeft residual_pos pivot).firstOrder ≠ 0)
  | rightPreterminal
      (residual_pos : 0 < B.clock.residualDefect)
      (pivot : B.clock.tailSeries.RightAxisPivot)
      (firstOrder_lt :
        (B.clock.toRankOneClockRight residual_pos pivot).firstOrder <
          (B.clock.toRankOneClockRight residual_pos pivot).defect)
      (offDiag_ne :
        (B.clock.toRankOneClockRight residual_pos pivot).series.offDiag.coeff
          (B.clock.toRankOneClockRight residual_pos pivot).firstOrder ≠ 0)
  | rightExactClosing
      (residual_pos : 0 < B.clock.residualDefect)
      (pivot : B.clock.tailSeries.RightAxisPivot)
      (firstOrder_eq :
        (B.clock.toRankOneClockRight residual_pos pivot).firstOrder =
          (B.clock.toRankOneClockRight residual_pos pivot).defect)
      (kernel_ne :
        (B.clock.toRankOneClockRight residual_pos pivot).series.kernel.coeff
          (B.clock.toRankOneClockRight residual_pos pivot).firstOrder ≠ 0)

/-- **D4: finite closure of the zero-relative binary alternatives.** -/
theorem ZeroRelativeExplicitBinaryClockData.endpointSplit
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    (B : P.ZeroRelativeExplicitBinaryClockData S) :
    Nonempty (P.ZeroRelativeExplicitBinaryEndpointSplit B) := by
  by_cases hres0 : B.clock.residualDefect = 0
  · exact ⟨.determinantClosing hres0
      (B.clock.tail_constant_det_ne_zero_of_residual_zero hres0)⟩
  · have hres : 0 < B.clock.residualDefect := Nat.pos_of_ne_zero hres0
    rcases B.clock.tail_pivot_of_residual_pos hres with hleft | hright
    · rcases lt_or_eq_of_le
          (B.clock.toRankOneClockLeft hres hleft).firstOrder_le_defect with
        hpre | hclose
      · exact ⟨.leftPreterminal hres hleft hpre
          ((B.clock.toRankOneClockLeft hres hleft).
            offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre)⟩
      · exact ⟨.leftExactClosing hres hleft hclose
          (exactRankOneSchurClockAt_kernel_coeff_firstOrder_ne_zero_of_closing
            (B.clock.toRankOneClockLeft hres hleft) hclose)⟩
    · rcases lt_or_eq_of_le
          (B.clock.toRankOneClockRight hres hright).firstOrder_le_defect with
        hpre | hclose
      · exact ⟨.rightPreterminal hres hright hpre
          ((B.clock.toRankOneClockRight hres hright).
            offDiag_coeff_firstOrder_ne_zero_of_preterminal hpre)⟩
      · exact ⟨.rightExactClosing hres hright hclose
          (exactRankOneSchurClockAt_kernel_coeff_firstOrder_ne_zero_of_closing
            (B.clock.toRankOneClockRight hres hright) hclose)⟩

/-- Assembly-facing zero-relative frontier after the binary clock has been
fully reduced to its finite preterminal/closing alternatives. -/
inductive TopKernelThreeSchurZeroRelativeFiniteFrontier
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
  | binaryEndpoint
      (tail : ThreeSchurTangentTailKernelOpeningData S M)
      (relative_eq_zero : tail.relativeOrder = 0)
      (constantKernelOpening :
        S.toExactZeroThreeSchurClock.tailConstantMatrix
          tail.physical.index 2 ≠ 0)
      (residual_pos :
        0 < S.toExactZeroThreeSchurClock.residualDefect)
      (binary : P.ZeroRelativeExplicitBinaryClockData S)
      (endpoint : P.ZeroRelativeExplicitBinaryEndpointSplit binary)

/-- Every D3 binary frontier reaches the complete finite D4 split. -/
theorem TopKernelThreeSchurZeroRelativeBinaryFrontier.toFiniteFrontier
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    {S : P.TopKernelThreeSchurClockData}
    {M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak}
    (F : P.TopKernelThreeSchurZeroRelativeBinaryFrontier S M) :
    Nonempty (P.TopKernelThreeSchurZeroRelativeFiniteFrontier S M) := by
  cases F with
  | determinantClosing tail hz hopen hres hdet =>
      exact ⟨.determinantClosing tail hz hopen hres hdet⟩
  | representedSchur tail hz hopen geometry =>
      exact ⟨.representedSchur tail hz hopen geometry⟩
  | explicitBinary tail hz hopen hres binary =>
      rcases binary.endpointSplit with ⟨endpoint⟩
      exact ⟨.binaryEndpoint tail hz hopen hres binary endpoint⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
