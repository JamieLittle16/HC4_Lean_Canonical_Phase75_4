import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisLinearPowerBoundaryFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisFullFacetReduced
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelLinearPowerCDSourceFrontier
import Mathlib.Tactic

/-!
# E2: combined source-honest frontier for one top-kernel linear power

The marked-axis and C/D analyses describe the same retained linear-power top
face, but until this file their outputs lived behind separate frontiers.

This module intersects those two green classifications without weakening
either one.  In the full marked-facet branch it also immediately consumes the
already-green lower-contact reduction, so callers never see the unreduced
full-facet constructor again.

The resulting finite frontier retains:

* the exact pure-longitudinal top power, or
* an explicit codimension-two endpoint, or
* an actual represented-source rank-two Hessian chart,

together with the complete source-honest C/D frontier of the same packet.

No progress label is treated as a contradiction and no terminal endpoint is
manufactured here.
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

/-- Combined E2 output for one literal linear-power top face. -/
inductive TopKernelLinearPowerE2Frontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | pureLongitudinal
      (coefficient : K)
      (coefficient_ne_zero : coefficient ≠ 0)
      (topFace_eq :
        T.topFace.face =
          MvPolynomial.C coefficient *
            (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree)
      (kernel_ne_zero : kernelCoordinate ≠ (0 : Fin 4))
      (cd : P.TopKernelLinearPowerCDSourceFrontier)
  | fullFacetCodimensionTwo
      (topFaceOnMarkedFacet :
        HC4.Polynomial.MvSupportOnFacet .qs T.topFace.face)
      (boundary :
        MvExponentOnCodimensionTwoBoundary
          (P.fullMarkedFacetRayFacetExponent topFaceOnMarkedFacet))
      (cd : P.TopKernelLinearPowerCDSourceFrontier)
  | fullFacetActualRankTwo
      (topFaceOnMarkedFacet :
        HC4.Polynomial.MvSupportOnFacet .qs T.topFace.face)
      (geometry :
        AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented)
      (cd : P.TopKernelLinearPowerCDSourceFrontier)
  | crossFacetNear
      (data :
        CrossFacetInitialData T.topFace.face
          (crossFacetOppositeCoordinate (0 : Fin 4))
          (0 : Fin 4))
      (boundary :
        MvExponentOnCodimensionTwoBoundary
          (P.markedAxisCrossFacetNormalizedRay data).facetExponent)
      (cd : P.TopKernelLinearPowerCDSourceFrontier)
  | crossFacetFar
      (data :
        CrossFacetInitialData T.topFace.face
          (crossFacetOppositeCoordinate (0 : Fin 4))
          (0 : Fin 4))
      (boundary :
        MvExponentOnCodimensionTwoBoundary
          (P.markedAxisCrossFacetFarExponent data))
      (cd : P.TopKernelLinearPowerCDSourceFrontier)

/-- **Combined E2 assembly.**

The two independent green analyses can be chosen simultaneously because they
are deterministic proposition-valued classifications of the same retained
packet.  The only extra case split is the already-proved reduction of complete
marked-facet confinement. -/
theorem topKernelLinearPowerE2Frontier_nonempty
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty P.TopKernelLinearPowerE2Frontier := by
  let C := P.topKernelLinearPowerCDSourceFrontier
  cases P.topKernelMarkedAxisLinearPowerBoundaryFrontier with
  | pureLongitudinal b hb hface hk =>
      exact ⟨.pureLongitudinal b hb hface hk C⟩
  | fullMarkedFacet hfacet _hsupp =>
      rcases P.fullMarkedFacetReducedFrontier_nonempty hfacet with ⟨R⟩
      cases R with
      | startCodimensionTwo htwo =>
          exact ⟨.fullFacetCodimensionTwo hfacet htwo C⟩
      | actualRankTwo A =>
          exact ⟨.fullFacetActualRankTwo hfacet A C⟩
  | crossFacetNear data htwo =>
      exact ⟨.crossFacetNear data htwo C⟩
  | crossFacetFar data htwo =>
      exact ⟨.crossFacetFar data htwo C⟩

/-- Canonical Type-valued combined E2 frontier. -/
noncomputable def topKernelLinearPowerE2Frontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    P.TopKernelLinearPowerE2Frontier :=
  Classical.choice P.topKernelLinearPowerE2Frontier_nonempty

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
