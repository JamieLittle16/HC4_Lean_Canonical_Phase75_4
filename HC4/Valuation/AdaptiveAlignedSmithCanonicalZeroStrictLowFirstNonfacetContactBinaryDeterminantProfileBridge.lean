import HC4.Newton.GeneralFourBlockDeterminantCovariance
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinarySchurProfileBridge
import Mathlib.Tactic

/-!
# A19.R18: shifted straightened determinant clock

R20 now exposes the source-first full Hessian determinant clock at the shifted
profile order

    2 * D - profileWeight * n + 4.

The R18 staircase extraction is performed after Euler row/column scaling and
the weighted-Euler second-complement shear.  Neither operation changes the
parameter order: Euler scaling contributes only a fixed source monomial, and
the shear has unit genuine quotient coefficient.  Thus the shifted source
clock transports literally to the straightened full determinant.

This is the full-determinant companion of
`binaryWeightedEulerShear_parameterLayer_profileOrder_eq_zero`.  No active
pivot is divided out here; the next cancellation remains integral.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Fixed source-coordinate monomial introduced by Euler scaling of the full
four-by-four determinant. -/
noncomputable def binaryEulerDeterminantSourceFactor
    (rho : Equiv.Perm (Fin 4)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  (MvPolynomial.X (rho 0) * MvPolynomial.X (rho 1)) ^ 2 *
    (MvPolynomial.X (rho 2) * MvPolynomial.X (rho 3)) ^ 2

/-- Ground-field form of the Euler determinant source factor. -/
noncomputable def binaryEulerDeterminantSourceFactorBase
    (rho : Equiv.Perm (Fin 4)) :
    MvPolynomial (Fin 4) K :=
  (MvPolynomial.X (rho 0) * MvPolynomial.X (rho 1)) ^ 2 *
    (MvPolynomial.X (rho 2) * MvPolynomial.X (rho 3)) ^ 2

/-- The polynomial-coefficient determinant factor is the constant lift of its
ground-field source monomial. -/
theorem binaryEulerDeterminantSourceFactor_eq_map_C
    (rho : Equiv.Perm (Fin 4)) :
    binaryEulerDeterminantSourceFactor (K := K) rho =
      MvPolynomial.map Polynomial.C
        (binaryEulerDeterminantSourceFactorBase (K := K) rho) := by
  simp [binaryEulerDeterminantSourceFactor,
    binaryEulerDeterminantSourceFactorBase]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- **R18 exact full-determinant representation bridge.**  Weighted-Euler
straightening has unit determinant, while Euler scaling contributes only the
fixed displayed source monomial. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryWeightedEulerShear_determinantCore_eq_sourceFactor_mul
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4)) :
    (P.binaryWeightedEulerShear rho).determinantCore =
      binaryEulerDeterminantSourceFactor (K := K) rho *
        (permutedPolynomialHessianFourBlock
          rho P.binaryHomogenizedFamily).determinantCore := by
  rw [QsOtherFacetContactQuadraticReesPackage.binaryWeightedEulerShear]
  rw [GeneralFourBlock.determinantCore_shearSecondComplement]
  simp only [one_pow, one_mul]
  rw [QsOtherFacetContactQuadraticReesPackage.binaryEulerHessianFourBlock]
  rw [permutedEulerScaledHessianFourBlock_eq_diagonalScale]
  rw [GeneralFourBlock.determinantCore_diagonalScale]
  unfold binaryEulerDeterminantSourceFactor
  ring

/-- **R18 shifted straightened full-determinant clock.**  Every layer that can
carry the active-pivot multiple of a degree-`n` staircase determinant
coefficient is zero after the full weighted-Euler straightening. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryWeightedEulerShear_determinantCore_parameterLayer_profileOrder_add_four_eq_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4))
    (n : ℕ) :
    familyParameterLayer
        (P.binaryWeightedEulerShear rho).determinantCore
        ((2 * T.topFace.degree - P.profileWeight * n) + 4) = 0 := by
  rw [P.binaryWeightedEulerShear_determinantCore_eq_sourceFactor_mul rho]
  rw [binaryEulerDeterminantSourceFactor_eq_map_C]
  rw [familyParameterLayer_map_C_mul]
  rw [P.binaryHomogenized_permutedSourceDeterminantCore_parameterLayer_profileOrder_add_four_eq_zero
    rho n]
  simp

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
