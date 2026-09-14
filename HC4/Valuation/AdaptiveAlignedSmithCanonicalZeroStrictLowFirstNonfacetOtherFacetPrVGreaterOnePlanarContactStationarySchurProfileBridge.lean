import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryEulerSchur
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryActivePivot
import HC4.Valuation.PermutedPolynomialHessianFourBlock
import Mathlib.Tactic

/-!
# A19 stationary Schur/profile bridge

The stationary Euler-Schur block lives source-first over
`MvPolynomial (Fin 4) (Polynomial K)`, whereas the previously established
stationary active-pivot certificate is stated after the parameter-first ring
equivalence.  Before identifying the Schur quotient with the stationary
profile Hessian, record the exact integral cancellation interface in the
source-first ring.

The Euler-scaled active determinant is the ordinary stationary Hessian active
determinant multiplied by the square of the genuine source monomial
`X₂ * X₃`.  The ordinary active determinant is nonzero because its
parameter-first image has nonzero constant parameter coefficient.  The pair
weighted-Euler shear does not change the active block.  Hence the sheared
active determinant is nonzero and can be cancelled without localization or
division.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- The ordinary source-first `(2,3)` active determinant of the stationary
ramified family is nonzero.  This is exactly the source-side transport of the
already verified nonzero constant coefficient of the parameter-first pivot. -/
theorem stationaryRamifiedFamily_sourceActiveDet_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (permutedPolynomialHessianFourBlock
      qsPrSuperfaceSchurPermutation D.stationaryRamifiedFamily).activeDet ≠ 0 := by
  intro hzero
  have hfamily :
      (permutedFamilyHessianFourBlock
        qsPrSuperfaceSchurPermutation D.stationaryRamifiedFamily).activeDet = 0 := by
    rw [permutedFamilyHessianFourBlock_activeDet_eq_parameterFirstEquiv]
    rw [hzero]
    simp
  have hcoeff :=
    D.stationaryRamifiedFamily_activeDet_coeff_zero_ne_zero hthree houtThree
  apply hcoeff
  rw [hfamily]
  simp

/-- Euler scaling preserves nonvanishing of the stationary active pivot. -/
theorem stationaryEulerHessianFourBlock_activeDet_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    D.stationaryEulerHessianFourBlock.activeDet ≠ 0 := by
  rw [stationaryEulerHessianFourBlock]
  rw [permutedEulerScaledHessianFourBlock_eq_diagonalScale]
  rw [GeneralFourBlock.activeDet_diagonalScale]
  apply mul_ne_zero
  · exact pow_ne_zero 2
      (mul_ne_zero
        (MvPolynomial.X_ne_zero (qsPrSuperfaceSchurPermutation 0))
        (MvPolynomial.X_ne_zero (qsPrSuperfaceSchurPermutation 1)))
  · exact D.stationaryRamifiedFamily_sourceActiveDet_ne_zero hthree houtThree

/-- The pair weighted-Euler shear leaves the genuine source-first active pivot
nonzero. -/
theorem stationaryPairWeightedEulerShear_activeDet_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    D.stationaryPairWeightedEulerShear.activeDet ≠ 0 := by
  rw [D.stationaryPairWeightedEulerShear_activeDet]
  exact D.stationaryEulerHessianFourBlock_activeDet_ne_zero hthree houtThree

/-- Integral source-first cancellation by the sheared stationary active pivot.
No fraction field or inverse is introduced. -/
theorem cancel_stationaryPairWeightedEulerShear_activeDet
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (B : MvPolynomial (Fin 4) (Polynomial K))
    (hprod : D.stationaryPairWeightedEulerShear.activeDet * B = 0) :
    B = 0 := by
  exact (mul_eq_zero.mp hprod).resolve_left
    (D.stationaryPairWeightedEulerShear_activeDet_ne_zero hthree houtThree)

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
