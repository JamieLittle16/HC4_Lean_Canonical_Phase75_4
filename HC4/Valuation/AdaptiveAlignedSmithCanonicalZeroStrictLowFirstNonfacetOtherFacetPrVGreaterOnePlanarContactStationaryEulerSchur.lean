import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryCarrierEuler
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationarySchurSingularity
import HC4.Valuation.PermutedPolynomialHessianFourBlock
import Mathlib.Tactic

/-!
# A19 stationary Euler-scaled Schur shear

The stationary ramified planar-contact family is already globally
Hessian-singular and carries the exact weighted Euler relation

    E_tau Q + r Q = r E_0 Q + r E_1 Q.

For the `.pr` active pair `(2,3)`, the complementary source directions are
therefore `(0,1)`.  This module first passes the source Hessian to its
Euler-scaled `2+2` four-block and then replaces the second complementary
direction by the honest pair direction

    r E_1 + r E_0.

This is only a `GeneralFourBlock.shearSecondComplement`, so no quotient,
division, localization, or clock identification is introduced.  The cleared
Schur determinant stays identically zero.  The following module may therefore
identify the three sheared complementary entries with the stationary profile
Hessian without reopening the determinant argument.
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

/-- Euler-scaled Hessian of the stationary ramified family in the `.pr`
active/complement order `(2,3 | 0,1)`. -/
noncomputable def stationaryEulerHessianFourBlock
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    GeneralFourBlock (MvPolynomial (Fin 4) (Polynomial K)) :=
  GeneralFourBlock.ofSymmetricMatrix
    ((HC4.Polynomial.eulerScaledHessian D.stationaryRamifiedFamily).submatrix
      qsPrSuperfaceSchurPermutation qsPrSuperfaceSchurPermutation)

/-- Replace the second complementary source direction by
`r E_1 + r E_0`, where `r = stationaryWeight`.  Active-span coefficients are
zero; the later carrier-Euler equations are used only when identifying the
resulting entries. -/
noncomputable def stationaryPairWeightedEulerShear
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    GeneralFourBlock (MvPolynomial (Fin 4) (Polynomial K)) :=
  D.stationaryEulerHessianFourBlock.shearSecondComplement
    (F.stationaryWeight : MvPolynomial (Fin 4) (Polynomial K))
    (F.stationaryWeight : MvPolynomial (Fin 4) (Polynomial K)) 0 0

/-- The Euler-scaled stationary four-block has zero cleared Schur determinant.
Euler scaling is diagonal congruence by source-coordinate monomials, so this
is a direct transport of the already-proved stationary Hessian singularity. -/
theorem stationaryEulerHessianFourBlock_schurDetCore_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    D.stationaryEulerHessianFourBlock.schurDetCore = 0 := by
  rw [stationaryEulerHessianFourBlock]
  rw [permutedEulerScaledHessianFourBlock_eq_diagonalScale]
  rw [GeneralFourBlock.schurDetCore_diagonalScale]
  rw [permutedPolynomialHessianFourBlock_schurDetCore_eq_zero
    qsPrSuperfaceSchurPermutation D.stationaryRamifiedFamily
    D.stationaryRamifiedFamily_hessianDeterminant_eq_zero]
  simp

/-- **Stationary sheared Schur singularity.**  The pair weighted-Euler shear
changes the cleared Schur determinant only by the square of its genuine second
complement coefficient.  Since the unsheared determinant is already zero, the
straightened determinant is identically zero as well. -/
theorem stationaryPairWeightedEulerShear_schurDetCore_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    D.stationaryPairWeightedEulerShear.schurDetCore = 0 := by
  rw [stationaryPairWeightedEulerShear]
  rw [GeneralFourBlock.schurDetCore_shearSecondComplement]
  rw [D.stationaryEulerHessianFourBlock_schurDetCore_eq_zero]
  simp

/-- The pair shear does not alter the active `(2,3)` pivot. -/
@[simp] theorem stationaryPairWeightedEulerShear_activeDet
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    D.stationaryPairWeightedEulerShear.activeDet =
      D.stationaryEulerHessianFourBlock.activeDet := by
  simp [stationaryPairWeightedEulerShear]

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
