import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3CodimensionTwoSourceRankTwoFrontier
import Mathlib.Tactic

/-!
# Reachable nonlinear E3 lower face: source-rank-two-aware finite frontier

The quadratic first-actual transverse layer has already been ruled out
by the exact marked source collision.  In the genuinely nonlinear
lower-face case the canonical singular-boundary theorem exposes either
a rank-three *support exponent on a toric facet* or a codimension-two
boundary exponent.

For the latter, the canonical coordinate-max opening is reconstructed
with exact three-step provenance and its child's Hessian rank-two
witness is lifted back to the literal represented determinant-one
source.  This removes the *auxiliary-child-only* rank-two outcome from
the E3 frontier.

The resulting five constructors are distinct mathematical alternatives.
In particular, the rank-three support exponent is not a rank-three
Hessian certificate, and a nonzero source 2x2 Hessian minor by itself
is not a final-resolution witness.
-/

namespace HC4.Valuation
noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
namespace TopFaceLinearPowerKernelData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {kernelCoordinate : Fin 4}

/-- Entire reachable nonlinear first-actual E3 lower-face frontier, now with
represented-source rather than descendant-child Hessian rank-two geometry. -/
inductive PureLongitudinalMarkedE3NonlinearSourceRankTwoFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | facetSupport
      (N : P.PureLongitudinalMarkedAxisLowerNonlinearData)
      (facet : HC4.Toric.ToricFacet)
      (hfacet : MvRankThreeOnFacet facet N.vertex.exponent)
  | lowerFaceKernel
      (N : P.PureLongitudinalMarkedAxisLowerNonlinearData)
      (coordinate : Fin 4)
      (hkernel :
        MvPolynomial.pderiv coordinate
          (familyParameterLayer
            T.topKernelMarkedAxisFirstContactFamily
            T.topKernelMarkedAxisFirstActualLayerOrder) = 0)
  | transverseFirstOpening
      (N : P.PureLongitudinalMarkedAxisLowerNonlinearData)
      (O : CanonicalCoordinateMaxKernelOpeningData
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder))
      (htrans : O.kernelCoordinate ≠ (0 : Fin 4))
  | representedSourceRankTwo
      (N : P.PureLongitudinalMarkedAxisLowerNonlinearData)
      (i j k l : Fin 4)
      (hminor : hessianTwoByTwoMinor T.topKernelReesSource i j k l ≠ 0)
  | longitudinalPowerFirstBreak
      (N : P.PureLongitudinalMarkedAxisLowerNonlinearData)
      (O : CanonicalCoordinateMaxKernelOpeningData
        (familyParameterLayer
          T.topKernelMarkedAxisFirstContactFamily
          T.topKernelMarkedAxisFirstActualLayerOrder))
      (hlong : O.kernelCoordinate = (0 : Fin 4))
      (LP : O.ChildLinearPowerData
        (T.topFace.degree - T.topKernelMarkedAxisFirstActualLayerOrder))
      (hbreak :
        let B := kernelLastFamilyHessianFourBlock
          O.reverseReesFamily O.kernelCoordinate
        let hrow := O.kernelLastBlock_kernelRow_ne_zero
          N.support_degree_ge_three
        let j := firstFourBlockKernelRowBreakOrder B hrow
        RankOneSpecialFiberFirstBreakOutcome B j)

/-- The entire reachable pure-longitudinal E3 first actual face has one of
five source-honest nonlinear outcomes.  The old quadratic constructor
is contradicted by the determinant-one source marked-axis collision;
the codimension-two branch uses the proven canonical opening
provenance to lift every child-rank-two outcome to the original source. -/
theorem PureLongitudinalMarkedE3Data.nonlinearSourceRankTwoFrontier_nonempty
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : P.PureLongitudinalMarkedE3Data) :
    Nonempty P.PureLongitudinalMarkedE3NonlinearSourceRankTwoFrontier := by
  rcases P.pureLongitudinal_markedAxis_lowerBoundaryFrontier_nonempty
      D.coefficient_ne_zero D.topFace_eq with ⟨H⟩
  cases H with
  | quadratic hr =>
      exact (D.quadratic_relevel_impossible P hr).elim
  | rankThree N facet hfacet =>
      exact ⟨.facetSupport N facet hfacet⟩
  | kernelOpening N _outcome =>
      rcases mvBoundary_rankThreeFacet_or_codimensionTwo
          N.vertex.exponent_boundary with hthree | hcodim
      · rcases hthree with ⟨facet, hfacet⟩
        exact ⟨.facetSupport N facet hfacet⟩
      · rcases D.codimensionTwoLowerFace_sourceRankTwoFrontier
            P N hcodim with hkernel | htrans | hsource | hpower
        · rcases hkernel with ⟨k, hk⟩
          exact ⟨.lowerFaceKernel N k hk⟩
        · rcases htrans with ⟨O, hO⟩
          exact ⟨.transverseFirstOpening N O hO⟩
        · rcases hsource with ⟨i, j, k, l, hminor⟩
          exact ⟨.representedSourceRankTwo N i j k l hminor⟩
        · rcases hpower with ⟨O, hlong, LP, hbreak⟩
          exact ⟨.longitudinalPowerFirstBreak N O hlong LP hbreak⟩

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end
end HC4.Valuation
