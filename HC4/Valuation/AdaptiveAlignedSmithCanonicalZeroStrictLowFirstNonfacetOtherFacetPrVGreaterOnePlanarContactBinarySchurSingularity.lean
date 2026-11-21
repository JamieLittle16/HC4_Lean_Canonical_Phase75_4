import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactBinaryProfileHessianEulerReduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactFamilyActiveConstant
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinarySchurProfileBridge
import Mathlib.Tactic

/-!
# A19 global Schur singularity of the planar binary family

The generic contact route only knows a finite source determinant clock.  The
planar-contact carrier is stronger: its reverse-Rees family has identically
zero Hessian determinant, and simultaneous transverse inflation preserves that
singularity exactly.

After Euler scaling and the same weighted-Euler complementary shear used by
R18, the cleared Schur determinant is therefore identically zero.  This is a
global polynomial identity, not merely a below-clock statement.  It is the
source-honest determinant input for the final identification with the planar
binary profile Hessian.
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

/-- Euler-scaled Hessian four-block of the singular planar binary family. -/
noncomputable def binaryEulerHessianFourBlock
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (rho : Equiv.Perm (Fin 4)) :
    GeneralFourBlock (MvPolynomial (Fin 4) (Polynomial K)) :=
  GeneralFourBlock.ofSymmetricMatrix
    ((HC4.Polynomial.eulerScaledHessian D.binaryHomogenizedFamily).submatrix rho rho)

/-- Straighten the second complementary source direction by the pure binary
weight.  For `.pr` the ordered complement is `(x₀,x₁)`, exactly as in R18. -/
noncomputable def binaryWeightedEulerShear
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (rho : Equiv.Perm (Fin 4)) :
    GeneralFourBlock (MvPolynomial (Fin 4) (Polynomial K)) :=
  (D.binaryEulerHessianFourBlock rho).shearSecondComplement
    1 (D.binaryProfileWeight : MvPolynomial (Fin 4) (Polynomial K)) 1 1

/-- Euler scaling contributes only the fixed source monomial, while the unit
weighted-Euler shear preserves the cleared Schur determinant. -/
theorem binaryWeightedEulerShear_schurDetCore_eq_sourceFactor_mul
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (rho : Equiv.Perm (Fin 4)) :
    (D.binaryWeightedEulerShear rho).schurDetCore =
      binaryEulerSchurSourceFactor (K := K) rho *
        (permutedPolynomialHessianFourBlock
          rho D.binaryHomogenizedFamily).schurDetCore := by
  rw [binaryWeightedEulerShear]
  rw [GeneralFourBlock.schurDetCore_shearSecondComplement]
  simp only [one_pow, one_mul]
  rw [binaryEulerHessianFourBlock]
  rw [permutedEulerScaledHessianFourBlock_eq_diagonalScale]
  rw [GeneralFourBlock.schurDetCore_diagonalScale]
  unfold binaryEulerSchurSourceFactor
  ring

/-- **Global planar binary Schur singularity.**  Unlike the represented-source
contact family, no finite determinant clock is needed here: the whole
straightened cleared Schur determinant vanishes identically. -/
theorem binaryWeightedEulerShear_schurDetCore_eq_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (rho : Equiv.Perm (Fin 4)) :
    (D.binaryWeightedEulerShear rho).schurDetCore = 0 := by
  rw [D.binaryWeightedEulerShear_schurDetCore_eq_sourceFactor_mul rho]
  rw [permutedPolynomialHessianFourBlock_schurDetCore_eq_zero
    rho D.binaryHomogenizedFamily
    D.binaryHomogenizedFamily_hessianDeterminant_eq_zero]
  simp

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
