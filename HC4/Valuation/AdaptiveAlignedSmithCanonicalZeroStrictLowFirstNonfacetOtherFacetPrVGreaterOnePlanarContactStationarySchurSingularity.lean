import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryActivePivot
import HC4.Valuation.PermutedFamilyHessianFourBlock
import Mathlib.Tactic

/-!
# A19 stationary ramified Schur singularity

The stationary ramified family is globally Hessian-singular.  Passing its
actual Hessian to the parameter-first representation and simultaneously
permuting the source coordinates to the `.pr` active order preserves the full
determinant.  Hence the denominator-cleared complementary Schur determinant
vanishes identically.

This is the exact determinant input for the stationary profile-Hessian
recognition.  No pivot inversion is used; the nonzero active constant from the
preceding module is retained only for later integral cancellation.
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

/-- The actual parameter-first `.pr` four-block of the stationary ramified
source family has identically zero cleared Schur determinant. -/
theorem stationaryRamifiedFamily_permutedSchurDetCore_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    (permutedFamilyHessianFourBlock
      qsPrSuperfaceSchurPermutation D.stationaryRamifiedFamily).schurDetCore = 0 := by
  apply GeneralFourBlock.schurDetCore_eq_zero_of_determinantCore_eq_zero
  calc
    (permutedFamilyHessianFourBlock
        qsPrSuperfaceSchurPermutation D.stationaryRamifiedFamily).determinantCore =
        (permutedFamilyHessianFourBlock
          qsPrSuperfaceSchurPermutation D.stationaryRamifiedFamily).matrix.det :=
      (GeneralFourBlock.matrix_det _).symm
    _ = ((parameterFirstHessian D.stationaryRamifiedFamily).submatrix
          qsPrSuperfaceSchurPermutation qsPrSuperfaceSchurPermutation).det := by
      rw [permutedFamilyHessianFourBlock_matrix]
    _ = (parameterFirstHessian D.stationaryRamifiedFamily).det := by
      rw [Matrix.det_submatrix_equiv_self]
    _ = parameterFirstEquiv K
          (HC4.Polynomial.hessianDeterminant D.stationaryRamifiedFamily) := by
      exact parameterFirstHessian_det D.stationaryRamifiedFamily
    _ = 0 := by
      rw [D.stationaryRamifiedFamily_hessianDeterminant_eq_zero]
      simp

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
