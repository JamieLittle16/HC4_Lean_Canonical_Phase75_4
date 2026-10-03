import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelFirstBreakNonlinear
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelExactClock
import Mathlib.Tactic

/-!
# Nonlinear mixed sharpening of the zero-clock top-kernel first break

The detailed source-lift frontier retains the information discarded by the
older layer-only packet: on the first breaking ordinary layer the selected
kernel diagonal is still zero while one mixed kernel entry is nonzero.

The existing nonlinear sharpening already eliminates ordinary degrees zero,
one and two. Combining the two statements leaves exactly the residual needed
by the direction-lock / finite-staircase algebra:

* a strictly lower exact ordinary homogeneous source layer;
* ordinary degree at least three;
* zero Hessian diagonal in the stored top-kernel coordinate;
* a genuinely nonzero mixed Hessian entry in that same row.

The honest ordinary reverse-Rees family simultaneously retains its exact
determinant clock 4D - 8.

No terminal cocharacter, repair transition, no-successor hypothesis, or JC2
input is used.
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

/-- The genuine residual after both source lifting and low-degree
elimination. -/
structure ExactNonlinearMixedOrdinaryLayerAtFirstBreak
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1) where
  mixed : P.ExactMixedOrdinaryLayerAtFirstBreak
  sourceDegree_ge_three : 3 ≤ mixed.layer.sourceDegree

/-- The residual packet carries the exact ordinary reverse-Rees determinant
clock on the very same interpolation family. -/
theorem ExactNonlinearMixedOrdinaryLayerAtFirstBreak.exactClock
    {P : T.TopFaceLinearPowerKernelData kernelCoordinate}
    (M : P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak) :
    HasPolynomialFamilyHessianDefect
      (K := K)
      T.topKernelReverseReesFamily
      T.topKernelOrdinaryReesDefect :=
  T.topKernelReverseReesFamily_hasHessianDefect

/-- Nonlinear mixed top-kernel frontier.

Every top-kernel linear-power branch gives either an actual rank-two chart on
the represented determinant-one source, or an exact strictly lower nonlinear
ordinary source layer whose stored kernel direction is still diagonal-zero
but mixed-active. -/
theorem actualRankTwo_or_exactLowerNonlinearMixedLayer
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      Nonempty P.ExactNonlinearMixedOrdinaryLayerAtFirstBreak := by
  rcases P.actualRankTwo_or_exactLowerMixedOrdinaryLayer with
    hactual | hmixed
  · exact Or.inl hactual
  · rcases hmixed with ⟨M⟩
    have htwo : 2 ≤ M.layer.sourceDegree :=
      M.layer.sourceDegree_ge_two
    by_cases hdeg : M.layer.sourceDegree = 2
    · exact Or.inl
        ⟨M.layer.actualRankTwoChart_of_degree_eq_two hdeg⟩
    · exact Or.inr ⟨{
        mixed := M
        sourceDegree_ge_three := by omega
      }⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
