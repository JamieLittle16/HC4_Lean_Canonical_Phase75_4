import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinarySchurInflation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinarySourceSchurClock
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

/-- A parameter-free source polynomial factors straight through exact
parameter-layer extraction.  This is the generic plumbing used below for the
Euler source monomial. -/
theorem familyParameterLayer_map_C_mul
    (A : MvPolynomial (Fin 4) K)
    (F : MvPolynomial (Fin 4) (Polynomial K))
    (n : ℕ) :
    familyParameterLayer (MvPolynomial.map Polynomial.C A * F) n =
      A * familyParameterLayer F n := by
  classical
  apply MvPolynomial.ext
  intro d
  simp only [familyParameterLayer_coeff, MvPolynomial.coeff_mul]
  rw [Polynomial.finset_sum_coeff]
  apply Finset.sum_congr rfl
  intro b hb
  rw [MvPolynomial.coeff_map]
  rw [Polynomial.coeff_C_mul]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

-- CI anchor: elaborate the exact Euler-source-factor bridge on the refreshed inventory.

/-- Fixed source-coordinate monomial introduced by Euler scaling of the
cleared Schur determinant. -/
noncomputable def binaryEulerSchurSourceFactor
    (rho : Equiv.Perm (Fin 4)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  (MvPolynomial.X (rho 0) * MvPolynomial.X (rho 1)) ^ 4 *
    (MvPolynomial.X (rho 2) * MvPolynomial.X (rho 3)) ^ 2

/-- The same Euler source monomial over the ground field. -/
noncomputable def binaryEulerSchurSourceFactorBase
    (rho : Equiv.Perm (Fin 4)) :
    MvPolynomial (Fin 4) K :=
  (MvPolynomial.X (rho 0) * MvPolynomial.X (rho 1)) ^ 4 *
    (MvPolynomial.X (rho 2) * MvPolynomial.X (rho 3)) ^ 2

/-- The polynomial-coefficient Euler factor is literally the coefficientwise
constant lift of its ground-field source monomial. -/
theorem binaryEulerSchurSourceFactor_eq_map_C
    (rho : Equiv.Perm (Fin 4)) :
    binaryEulerSchurSourceFactor (K := K) rho =
      MvPolynomial.map Polynomial.C
        (binaryEulerSchurSourceFactorBase (K := K) rho) := by
  simp [binaryEulerSchurSourceFactor, binaryEulerSchurSourceFactorBase]

/-- The Euler source factor is a genuine nonzero monomial. -/
theorem binaryEulerSchurSourceFactor_ne_zero
    (rho : Equiv.Perm (Fin 4)) :
    binaryEulerSchurSourceFactor (K := K) rho ≠ 0 := by
  unfold binaryEulerSchurSourceFactor
  exact mul_ne_zero
    (pow_ne_zero 4
      (mul_ne_zero
        (MvPolynomial.X_ne_zero (rho 0))
        (MvPolynomial.X_ne_zero (rho 1))))
    (pow_ne_zero 2
      (mul_ne_zero
        (MvPolynomial.X_ne_zero (rho 2))
        (MvPolynomial.X_ne_zero (rho 3))))

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

/-- **R18 unrestricted straightened source clock.**  Every parameter layer
strictly before the exact binary Hessian clock vanishes after weighted-Euler
straightening.  The Euler source factor is parameter-free, so this is a direct
transport of the unrestricted R20 source-first Schur clock. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryWeightedEulerShear_parameterLayer_eq_zero_of_lt
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4))
    {q : ℕ}
    (hq : q < (4 * T.topFace.degree - 2 * (P.contactGap + 4)) + 6) :
    familyParameterLayer
        (P.binaryWeightedEulerShear rho).schurDetCore q = 0 := by
  rw [P.binaryWeightedEulerShear_schurDetCore_eq_sourceFactor_mul rho]
  rw [binaryEulerSchurSourceFactor_eq_map_C]
  rw [familyParameterLayer_map_C_mul]
  rw [P.binaryHomogenized_permutedSourceSchurDetCore_parameterLayer_eq_zero_of_lt
    rho hq]
  simp

/-- **R18 straightened source clock.**  The fixed Euler source monomial has no
parameter content, so every zero source-first Schur layer supplied by R20 is
also a zero layer of the straightened Euler-Schur determinant. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryWeightedEulerShear_parameterLayer_profileOrder_eq_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (Q : QsOtherFacetContactRawLongitudinalProfilePackage C P)
    (rho : Equiv.Perm (Fin 4))
    (n : ℕ) :
    familyParameterLayer
        (P.binaryWeightedEulerShear rho).schurDetCore
        (2 * T.topFace.degree - P.profileWeight * n) = 0 := by
  exact P.binaryWeightedEulerShear_parameterLayer_eq_zero_of_lt rho
    (P.binary_profileOrder_lt_hessianClock Q n)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation