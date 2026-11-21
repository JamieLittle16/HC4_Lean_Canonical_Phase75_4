import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseRightCentralRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCentralActualRankTwo
import Mathlib.Tactic

/-!
# Lift mirrored central finite-staircase rank-two geometry to the actual state

The right `(V,1)`, `V > 1` central branch already supplies an exact
coordinate-`0` maximal initial monomial with a nonzero principal Hessian minor
in coordinates `(0,2)`.  This file retains that source provenance and lifts the
minor first to the source-honest planar carrier and then to the actual presented
special fibre.

The resulting special-fibre minor is the constant coefficient of the active
determinant for the chart permutation `swap 1 2`, so the branch produces an
actual rank-two Hessian chart before any progress label is attached.
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

/-- Retained source-honest rank-two geometry at a right central point. -/
structure QsOtherFacetPrRightVCentralRankTwoGeometry
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R) where
  central : Fin 4 →₀ ℕ
  central_mem : central ∈ P.carrier.support
  central_one_zero : central 1 = 0
  central_three_zero : central 3 = 0
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
      exposure.face (0 : Fin 4) (2 : Fin 4) ≠ 0

/-- Package the already-verified right central coordinate-max theorem without
losing the source point or its two zero-coordinate witnesses. -/
theorem QsOtherFacetPrRightVContactFrontierData.centralRankTwoGeometry_of_point
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrRightVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {c : Fin 4 →₀ ℕ}
    (hc : c ∈ P.carrier.support)
    (hc1 : c 1 = 0)
    (hc3 : c 3 = 0) :
    Nonempty (QsOtherFacetPrRightVCentralRankTwoGeometry F) := by
  rcases F.central_coordinateMax_face_rankTwo
      hthree houtThree hc hc1 hc3 with
    ⟨D, hlevel, hface, hzero, hminor⟩
  exact ⟨{
    central := c
    central_mem := hc
    central_one_zero := hc1
    central_three_zero := hc3
    exposure := D
    exposure_level_eq := hlevel
    exposure_face_eq := hface
    exposure_hessian_zero := hzero
    exposure_rankTwo_minor := hminor
  }⟩

namespace QsOtherFacetPrRightVCentralRankTwoGeometry

variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrRightVContactFrontierData C P S R}

/-- Lift the exact central `(0,2)` minor to the source-honest planar carrier. -/
theorem carrier_hessianPrincipalMinor_ne_zero
    (G : QsOtherFacetPrRightVCentralRankTwoGeometry F) :
    HC4.Polynomial.hessianPrincipalMinor
      P.carrier (0 : Fin 4) (2 : Fin 4) ≠ 0 := by
  apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    G.exposure.weight_bound (0 : Fin 4) (2 : Fin 4)
  rw [← G.exposure.face_eq]
  exact G.exposure_rankTwo_minor

/-- Lift once more through the planar carrier's honest source exposure. -/
theorem presented_specialFiber_hessianPrincipalMinor_ne_zero
    (G : QsOtherFacetPrRightVCentralRankTwoGeometry F) :
    HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
      (0 : Fin 4) (2 : Fin 4) ≠ 0 := by
  apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    P.source_bound (0 : Fin 4) (2 : Fin 4)
  rw [← P.carrier_eq_initialForm]
  exact G.carrier_hessianPrincipalMinor_ne_zero

/-- The mirrored central branch is an actual rank-two Hessian chart on the
represented state. -/
noncomputable def actualRankTwoHessianChart
    (G : QsOtherFacetPrRightVCentralRankTwoGeometry F) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented := by
  let rho : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) 2
  refine {
    permutation := rho
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [rho] using G.presented_specialFiber_hessianPrincipalMinor_ne_zero

/-- Feed the actual right central chart into the existing rank-three geometry
consumer. -/
noncomputable def actualRankThreeGeometry
    (G : QsOtherFacetPrRightVCentralRankTwoGeometry F) :
    AdaptiveAlignedSmithCanonicalActualRankThreeGeometry
      G.actualRankTwoHessianChart 0 :=
  G.actualRankTwoHessianChart.rankThreeGeometry 0

end QsOtherFacetPrRightVCentralRankTwoGeometry

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
