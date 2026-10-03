import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelFirstBreakMixedNonlinear
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurClock
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelThreeSchurTangentSplit
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelRelativeGeometricFrontier
import Mathlib.Tactic

/-!
# Assembly-facing C/D geometry from every top-face linear-power packet

The top-kernel linear-power analysis has two stages before the already-finished
relative tail:

1. the first honest lower ordinary source layer either source-lifts directly
   to an actual represented-state rank-two Hessian chart, or is a nonlinear
   mixed first-break layer;
2. after choosing the exact 1+3 Schur clock, that mixed layer either already
   appears as a projected rank-two coefficient block, or is tangent and enters
   the exact relative-order split.

The tangent side is completely consumed by
`TopKernelThreeSchurRelativeGeometricFrontier`, whose zero- and
positive-relative branches are already source-honest.

This file performs only that assembly.  It deliberately retains the projected
rank-two first-break alternative as the single pre-relative geometric seam;
it does not pretend that a quotient coefficient matrix is itself a source
Hessian or a terminal polynomial endpoint.
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

/-- Complete assembly-facing geometry before terminal extraction.

Only the `projectedRankTwo` constructor is not already represented-source
geometry.  It retains the exact source layer, exact 1+3 clock, and the literal
projected coefficient witness needed for a dedicated source-lift adapter. -/
inductive TopKernelLinearPowerCDGeometricFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | actualRankTwo
      (geometry :
        AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented)
  | projectedRankTwo
      (layer : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak)
      (clock : P.TopKernelThreeSchurClockData)
      (geometry :
        ThreeSchurProjectedRankTwoAtFirstBreak clock layer)
  | relative
      (layer : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak)
      (clock : P.TopKernelThreeSchurClockData)
      (tangent : ThreeSchurTangentAtFirstBreak clock layer)
      (geometry : P.TopKernelThreeSchurRelativeGeometricFrontier clock layer)

/-- **C/D assembly from one linear-power top face.**

Every top-kernel linear-power packet reaches represented-source rank-two
geometry, the one explicit projected-rank-two first-break seam, or the already
complete zero/positive relative geometric frontier. -/
theorem topKernelLinearPowerCDGeometricFrontier_nonempty
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty P.TopKernelLinearPowerCDGeometricFrontier := by
  rcases P.actualRankTwo_or_exactLowerNonlinearMixedLayer with
    hactual | hlayer
  · rcases hactual with ⟨A⟩
    exact ⟨.actualRankTwo A⟩
  · rcases hlayer with ⟨M⟩
    rcases P.threeSchurClockData with ⟨S⟩
    rcases projectedRankTwo_or_tangentAtFirstBreak S M with
      hprojected | htangent
    · exact ⟨.projectedRankTwo M S hprojected⟩
    · rcases htangent.relativeGeometricFrontier with ⟨G⟩
      exact ⟨.relative M S htangent G⟩

/-- Canonical Type-valued C/D assembly frontier. -/
noncomputable def topKernelLinearPowerCDGeometricFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    P.TopKernelLinearPowerCDGeometricFrontier :=
  Classical.choice P.topKernelLinearPowerCDGeometricFrontier_nonempty

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
