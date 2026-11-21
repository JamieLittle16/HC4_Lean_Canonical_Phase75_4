import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryEulerSchur
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryActivePivot
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryFamilyBridge
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

Finally, move the globally vanishing sheared Schur determinant through the
canonical parameter-first equivalence and the already existing rank-three line
specialisation.  This lands the zero determinant in exactly the integral ring
`Polynomial (Polynomial K)` occupied by the stationary carrier profile.  The
remaining bridge can therefore be stated as a literal polynomial identity in
one ring, with no representation coercions left.
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

/-- Cancelling the genuine source-first active pivot from the cleared Schur
identity leaves the full determinant core of the weighted-Euler sheared block
identically zero. -/
theorem stationaryPairWeightedEulerShear_determinantCore_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    D.stationaryPairWeightedEulerShear.determinantCore = 0 := by
  apply D.cancel_stationaryPairWeightedEulerShear_activeDet hthree houtThree
  rw [← GeneralFourBlock.schurDetCore_eq_activeDet_mul_determinantCore]
  exact D.stationaryPairWeightedEulerShear_schurDetCore_eq_zero

/-- The sheared stationary Schur determinant, with the family parameter moved
outermost and the four source variables specialised to the canonical
rank-three line.  Its target ring is exactly the ring of the integral
stationary carrier profile. -/
noncomputable def specialisedStationarySchurDet
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    Polynomial (Polynomial K) :=
  Polynomial.map
    (HC4.Polynomial.rankThreeLineSpecialisation (K := K))
    (parameterFirstEquiv K D.stationaryPairWeightedEulerShear.schurDetCore)

/-- Global stationary Schur singularity survives the exact representation
change and rank-three line specialisation. -/
theorem specialisedStationarySchurDet_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    D.specialisedStationarySchurDet = 0 := by
  unfold specialisedStationarySchurDet
  rw [D.stationaryPairWeightedEulerShear_schurDetCore_eq_zero]
  simp

/-- Parameter-first, line-specialised determinant core of the same stationary
weighted-Euler sheared block. -/
noncomputable def specialisedStationaryDeterminantCore
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    Polynomial (Polynomial K) :=
  Polynomial.map
    (HC4.Polynomial.rankThreeLineSpecialisation (K := K))
    (parameterFirstEquiv K D.stationaryPairWeightedEulerShear.determinantCore)

/-- The source-first pivot cancellation remains zero after moving the parameter
outermost and specialising the honest rank-three line. -/
theorem specialisedStationaryDeterminantCore_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    D.specialisedStationaryDeterminantCore = 0 := by
  unfold specialisedStationaryDeterminantCore
  rw [D.stationaryPairWeightedEulerShear_determinantCore_eq_zero hthree houtThree]
  simp

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
