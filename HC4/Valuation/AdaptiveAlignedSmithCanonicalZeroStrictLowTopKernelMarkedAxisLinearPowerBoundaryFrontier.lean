import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisCrossFacetRefinement
import Mathlib.Tactic

/-!
# E2: consume the marked-axis cross-facet branch into codimension two

E1 reduces the residual top-kernel linear-power case to three support
geometries: a pure longitudinal top power, complete confinement to the marked
`.qs` facet, or an honest coordinate-zero cross-facet carrier on the actual
singular top face.

The cross-facet branch has now been analysed by the balance-free homogeneous
ray machinery.  Because the source top face is a scalar linear power, every
Hessian 2 x 2 minor vanishes, so the rank-two ray alternative is impossible.
The crossing therefore ends at one of the two explicit codimension-two
endpoints of the normalized ray.

This file performs only that assembly refinement.  No codimension-two endpoint
is yet declared terminal and no new Rees/Schur hierarchy is introduced.
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

/-- Far endpoint of the contact-normalized marked-axis cross-facet ray.

Naming the dependent projection avoids Lean parsing the normalized ray itself
as the argument of `zeroAffineLineData.exponent`. -/
noncomputable def markedAxisCrossFacetFarExponent
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate)
    (D : CrossFacetInitialData T.topFace.face
      (crossFacetOppositeCoordinate (0 : Fin 4))
      (0 : Fin 4)) : Fin 4 →₀ ℕ :=
  let R0 := P.markedAxisCrossFacetNormalizedRay D
  R0.zeroAffineLineData.exponent R0.zeroCoefficientPolynomial.natDegree

/-- E2 frontier after consuming the genuine cross-facet branch. -/
inductive TopKernelMarkedAxisLinearPowerBoundaryFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) : Type (u + 1)
  | pureLongitudinal
      (coefficient : K)
      (coefficient_ne_zero : coefficient ≠ 0)
      (topFace_eq :
        T.topFace.face =
          MvPolynomial.C coefficient *
            (MvPolynomial.X (0 : Fin 4)) ^ T.topFace.degree)
      (kernel_ne_zero : kernelCoordinate ≠ (0 : Fin 4))
  | fullMarkedFacet
      (topFaceOnMarkedFacet :
        HC4.Polynomial.MvSupportOnFacet .qs T.topFace.face)
      (support_eq :
        (polynomialFamilySpecialFiber
          T.topKernelMarkedAxisFirstContactFamily).support =
            T.topFace.face.support)
  | crossFacetNear
      (data :
        CrossFacetInitialData T.topFace.face
          (crossFacetOppositeCoordinate (0 : Fin 4))
          (0 : Fin 4))
      (boundary :
        MvExponentOnCodimensionTwoBoundary
          (P.markedAxisCrossFacetNormalizedRay data).facetExponent)
  | crossFacetFar
      (data :
        CrossFacetInitialData T.topFace.face
          (crossFacetOppositeCoordinate (0 : Fin 4))
          (0 : Fin 4))
      (boundary :
        MvExponentOnCodimensionTwoBoundary
          (P.markedAxisCrossFacetFarExponent data))

/-- **E2 marked-axis boundary refinement.**

Every E1 linear-power frontier either remains in one of the two non-crossing
support cases or the crossing has already reached an explicit codimension-two
endpoint. -/
theorem topKernelMarkedAxisLinearPowerBoundaryFrontier_nonempty
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    Nonempty P.TopKernelMarkedAxisLinearPowerBoundaryFrontier := by
  rcases P.topKernelMarkedAxisLinearPowerFrontier_nonempty with ⟨F⟩
  cases F with
  | pureLongitudinal b hb hface hk =>
      exact ⟨.pureLongitudinal b hb hface hk⟩
  | fullMarkedFacet hfacet hsupp =>
      exact ⟨.fullMarkedFacet hfacet hsupp⟩
  | crossFacet data =>
      cases P.markedAxisCrossFacet_codimensionTwoFrontier data with
      | near hnear =>
          exact ⟨.crossFacetNear data hnear⟩
      | far hfar =>
          exact ⟨.crossFacetFar data (by
            simpa [markedAxisCrossFacetFarExponent] using hfar)⟩

/-- Canonical Type-valued E2 boundary frontier. -/
noncomputable def topKernelMarkedAxisLinearPowerBoundaryFrontier
    (P : T.TopFaceLinearPowerKernelData kernelCoordinate) :
    P.TopKernelMarkedAxisLinearPowerBoundaryFrontier :=
  Classical.choice P.topKernelMarkedAxisLinearPowerBoundaryFrontier_nonempty

end TopFaceLinearPowerKernelData
end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
