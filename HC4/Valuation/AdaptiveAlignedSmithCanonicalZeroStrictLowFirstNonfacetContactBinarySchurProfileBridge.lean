import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinarySchurInflation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFractionProfileRigidity
import Mathlib.Tactic

/-!
# A19.R18: straightened binary Schur determinant versus the source-first clock

The final staircase extraction uses the weighted-Euler straightened block,
while R20 kills parameter layers of the ordinary source-first Schur block.
There is no new determinant argument between those two representations.

Euler scaling is diagonal congruence by the four source coordinates, and the
R18 weighted shear has unit coefficient on its new complementary direction.
Consequently its Schur determinant is exactly the ordinary source-first Schur
determinant multiplied by the fixed source monomial

    (x_active0 x_active1)^4 (x_longitudinal x_omitted)^2.

The factor contains no family parameter.  This module freezes that exact
identity before the coefficientwise staircase extraction; no active pivot is
cancelled and no localization is introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- Fixed source-coordinate monomial introduced by Euler scaling of the
cleared Schur determinant. -/
noncomputable def binaryEulerSchurSourceFactor
    (rho : Equiv.Perm (Fin 4)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  (MvPolynomial.X (rho 0) * MvPolynomial.X (rho 1)) ^ 4 *
    (MvPolynomial.X (rho 2) * MvPolynomial.X (rho 3)) ^ 2

/-- The Euler source factor is a genuine nonzero monomial. -/
theorem binaryEulerSchurSourceFactor_ne_zero
    (rho : Equiv.Perm (Fin 4)) :
    binaryEulerSchurSourceFactor (K := K) rho ≠ 0 := by
  unfold binaryEulerSchurSourceFactor
  exact mul_ne_zero
    (pow_ne_zero 4 (mul_ne_zero MvPolynomial.X_ne_zero MvPolynomial.X_ne_zero))
    (pow_ne_zero 2 (mul_ne_zero MvPolynomial.X_ne_zero MvPolynomial.X_ne_zero))

/-- **R18 exact determinant representation bridge.**  Weighted-Euler
straightening preserves the Euler-scaled Schur determinant, and Euler scaling
itself contributes only the displayed fixed source monomial. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryWeightedEulerShear_schurDetCore_eq_sourceFactor_mul
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    (P.binaryWeightedEulerShear rho).schurDetCore =
      binaryEulerSchurSourceFactor (K := K) rho *
        (permutedPolynomialHessianFourBlock
          rho P.binaryHomogenizedFamily).schurDetCore := by
  rw [QsOtherFacetContactQuadraticReesPackage.binaryWeightedEulerShear]
  rw [GeneralFourBlock.schurDetCore_shearSecondComplement]
  simp only [one_pow, one_mul]
  rw [QsOtherFacetContactQuadraticReesPackage.binaryEulerHessianFourBlock]
  rw [permutedEulerScaledHessianFourBlock_eq_diagonalScale]
  rw [GeneralFourBlock.schurDetCore_diagonalScale]
  unfold binaryEulerSchurSourceFactor
  ring

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
