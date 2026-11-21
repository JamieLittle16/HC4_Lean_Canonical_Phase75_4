import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseRightCentralRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseCentralActualRankTwo
import Mathlib.Tactic

/-!
# Lift mirrored central unit finite-staircase rank-two geometry to the actual state

The right unit central branch supplies an exact coordinate-`0` maximal initial
monomial with a nonzero principal Hessian minor in coordinates `(0,2)`.  Lift
that minor through the honest planar carrier to the represented special fibre,
then package the corresponding actual rank-two Hessian chart.
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

structure QsOtherFacetPrUnitRightCentralRankTwoGeometry
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R) where
  central : Fin 4 →₀ ℕ
  central_mem : central ∈ P.carrier.support
  central_one_zero : central 1 = 0
  central_three_zero : central 3 = 0
  exposure : HC4.Newton.CoordinateMaxInitialData P.carrier (0 : Fin 4)
  exposure_level_eq : exposure.level = central 0
  exposure_face_eq :
    exposure.face = MvPolynomial.monomial central (MvPolynomial.coeff central P.carrier)
  exposure_hessian_zero : HC4.Polynomial.hessianDeterminant exposure.face = 0
  exposure_rankTwo_minor :
    HC4.Polynomial.hessianPrincipalMinor exposure.face (0 : Fin 4) (2 : Fin 4) ≠ 0

theorem QsOtherFacetPrUnitRightContactFrontierData.centralRankTwoGeometry_of_point
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {c : Fin 4 →₀ ℕ}
    (hc : c ∈ P.carrier.support) (hc1 : c 1 = 0) (hc3 : c 3 = 0) :
    Nonempty (QsOtherFacetPrUnitRightCentralRankTwoGeometry F) := by
  rcases F.central_coordinateMax_face_rankTwo hthree houtThree hc hc1 hc3 with
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

namespace QsOtherFacetPrUnitRightCentralRankTwoGeometry

variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrUnitRightContactFrontierData C P S R}

theorem carrier_hessianPrincipalMinor_ne_zero
    (G : QsOtherFacetPrUnitRightCentralRankTwoGeometry F) :
    HC4.Polynomial.hessianPrincipalMinor P.carrier (0 : Fin 4) (2 : Fin 4) ≠ 0 := by
  apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    G.exposure.weight_bound (0 : Fin 4) (2 : Fin 4)
  rw [← G.exposure.face_eq]
  exact G.exposure_rankTwo_minor

theorem presented_specialFiber_hessianPrincipalMinor_ne_zero
    (G : QsOtherFacetPrUnitRightCentralRankTwoGeometry F) :
    HC4.Polynomial.hessianPrincipalMinor
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
      (0 : Fin 4) (2 : Fin 4) ≠ 0 := by
  apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    P.source_bound (0 : Fin 4) (2 : Fin 4)
  rw [← P.carrier_eq_initialForm]
  exact G.carrier_hessianPrincipalMinor_ne_zero

noncomputable def actualRankTwoHessianChart
    (G : QsOtherFacetPrUnitRightCentralRankTwoGeometry F) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
      T.terminal.blocker.presented := by
  let rho : Equiv.Perm (Fin 4) := Equiv.swap (1 : Fin 4) 2
  refine {
    permutation := rho
    activeDet_coeff_zero_ne_zero := ?_
  }
  rw [scaleAwareHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  simpa [rho] using G.presented_specialFiber_hessianPrincipalMinor_ne_zero

noncomputable def actualRankThreeGeometry
    (G : QsOtherFacetPrUnitRightCentralRankTwoGeometry F) :
    AdaptiveAlignedSmithCanonicalActualRankThreeGeometry G.actualRankTwoHessianChart 0 :=
  G.actualRankTwoHessianChart.rankThreeGeometry 0

end QsOtherFacetPrUnitRightCentralRankTwoGeometry

/-- Thin constructor used by the final unit-right closure. -/
noncomputable def QsOtherFacetPrUnitRightContactFrontierData.central_actualRankTwoHessianChart
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {c : Fin 4 →₀ ℕ}
    (hc : c ∈ P.carrier.support) (hc1 : c 1 = 0) (hc3 : c 3 = 0) :
    AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart T.terminal.blocker.presented := by
  classical
  let G := Classical.choice (F.centralRankTwoGeometry_of_point hthree houtThree hc hc1 hc3)
  exact G.actualRankTwoHessianChart

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end
end HC4.Valuation
