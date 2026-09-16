import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelLinearPowerFirstBreak
import Mathlib.Tactic

/-!
# A19.55 final source-honest codimension-two geometry

The same-carrier codimension-two branch now has no generic-JC2 fallback.
Every branch is reduced to concrete rank-two Hessian geometry while retaining
the actual A19 strict-low source:

1. a nonzero Hessian `2 x 2` minor already on the honest maximal top face;
2. a nonzero Hessian `2 x 2` minor on an exact coordinate-max opening child;
3. rank-two geometry at the first honest kernel-row break of an exact
   coordinate-max opening child; or
4. rank-two geometry at the first honest ordinary-degree reverse-Rees break
   from a rank-one top face back to the represented determinant-one source.

The reverse-Rees parameters in (3) and (4) are auxiliary interpolation
parameters only.  No identification with the zero blocker clock is made, and
no repair-only progress is asserted in this file.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Complete source-honest rank-two outcome for the A19.55 codimension-two
branch.  There is intentionally no unresolved/default constructor. -/
inductive ExposedCodimensionTwoResolvedRankTwoGeometry
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Prop
  | topFace
      (h : T.TopFaceHessianRankTwoWitness)
  | openingChild
      (D : CanonicalCoordinateMaxKernelOpeningData T.topFace.face)
      (h : D.ChildHessianRankTwoWitness)
  | openingFirstBreak
      (D : CanonicalCoordinateMaxKernelOpeningData T.topFace.face)
      (P : D.ChildLinearPowerData T.topFace.degree)
      (h :
        let B := kernelLastFamilyHessianFourBlock
          D.reverseReesFamily D.kernelCoordinate
        let hrow := D.kernelLastBlock_kernelRow_ne_zero
          T.topFace.face_support_degree_ge_three
        let j := firstFourBlockKernelRowBreakOrder B hrow
        RankOneSpecialFiberFirstBreakOutcome B j)
  | topKernelFirstBreak
      (kernelCoordinate : Fin 4)
      (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
      (h :
        let B := kernelLastFamilyHessianFourBlock
          T.topKernelReverseReesFamily kernelCoordinate
        let hrow := T.topKernelLastBlock_kernelRow_ne_zero kernelCoordinate
        let j := firstFourBlockKernelRowBreakOrder B hrow
        RankOneSpecialFiberFirstBreakOutcome B j)

/-- **A19.55 codimension-two local closure.**

The actual exposed codimension-two strict-low terminal always carries one of
the four explicit rank-two geometries above.  In particular this branch does
not reduce to generic JC2. -/
theorem exposedCodimensionTwo_resolvedRankTwoGeometry
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hcodim : MvExponentOnCodimensionTwoBoundary
      T.exposedSingularBoundaryVertex.exponent) :
    T.ExposedCodimensionTwoResolvedRankTwoGeometry := by
  rcases T.exposedCodimensionTwo_topKernel_or_rankTwoGeometry hcodim with
    htop | hopening | hopeningBreak
  · rcases htop with ⟨k, hk⟩
    rcases T.topKernel_rankTwo_or_linearPower k hk with htwo | hpower
    · exact .topFace htwo
    · rcases hpower with ⟨P⟩
      exact .topKernelFirstBreak k P P.firstBreakRankTwoOutcome
  · rcases hopening with ⟨D, htwo⟩
    exact .openingChild D htwo
  · rcases hopeningBreak with ⟨D, P, hbreak⟩
    exact .openingFirstBreak D P hbreak

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
