import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCentralRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCrossRoofAffineTerminalRealisation
import Mathlib.Tactic

/-!
# Collapse the left finite-staircase roof split

The source-honest finite-staircase construction has only two outcomes:

* a central support monomial with source deficits `(e₁,e₂)=(0,0)`; or
* an honest exposed cross-roof singular face.

The second outcome is now impossible by the two oriented affine-line terminal
certificates.  The first outcome has already been turned into an exact
coordinate-`0` initial face carrying a nonzero principal Hessian minor.

Therefore the entire left `V>1` finite-staircase roof split compresses to one
concrete source-honest rank-two geometry package.  This file does not attach a
repair transition; the next assembly adapter may consume the retained geometry
without manufacturing progress from bookkeeping alone.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Retained source-honest rank-two geometry forced by the complete left
`V>1` finite-staircase roof analysis. -/
structure QsOtherFacetPrLeftVCentralRankTwoGeometry
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R) where
  central : Fin 4 →₀ ℕ
  central_mem : central ∈ P.carrier.support
  central_one_zero : central 1 = 0
  central_two_zero : central 2 = 0
  exposure : HC4.Newton.CoordinateMaxInitialData P.carrier (0 : Fin 4)
  exposure_level_eq : exposure.level = central 0
  exposure_face_eq :
    exposure.face =
      MvPolynomial.monomial central
        (MvPolynomial.coeff central P.carrier)
  exposure_hessian_zero :
    HC4.Polynomial.hessianDeterminant exposure.face = 0
  exposure_rankTwo_minor :
    HC4.Polynomial.hessianPrincipalMinor
      exposure.face (0 : Fin 4) (3 : Fin 4) ≠ 0

/-- **Complete left non-unit roof split: rank-two geometry survives.**

The exposed cross-roof alternative is contradictory, so the only surviving
finite-staircase outcome is the central coordinate-max monomial, together with
its exact nonzero `(0,3)` Hessian minor. -/
theorem QsOtherFacetPrLeftVContactFrontierData.centralRankTwoGeometry
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    Nonempty (QsOtherFacetPrLeftVCentralRankTwoGeometry F) := by
  rcases F.central_or_exposedCrossRoof hthree houtThree with
    hcentral | hexposed
  · rcases hcentral with ⟨c, hc, hc1, hc2⟩
    rcases F.central_coordinateMax_face_rankTwo
        hthree houtThree hc hc1 hc2 with
      ⟨D, hlevel, hface, hzero, hminor⟩
    exact ⟨{
      central := c
      central_mem := hc
      central_one_zero := hc1
      central_two_zero := hc2
      exposure := D
      exposure_level_eq := hlevel
      exposure_face_eq := hface
      exposure_hessian_zero := hzero
      exposure_rankTwo_minor := hminor
    }⟩
  · rcases hexposed with ⟨E⟩
    exact (E.impossible hthree houtThree).elim

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
