import HC4.Newton.GeneralFourBlockDeterminantCovariance
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinarySchurProfileBridge
import Mathlib.Algebra.Polynomial.Degree.TrailingDegree
import Mathlib.Tactic

/-!
# A19.R18: shifted straightened determinant clock

R20 exposes the source-first full Hessian determinant clock at the shifted
profile orders needed by the final cancellation.  The R18 staircase extraction
is performed after Euler row/column scaling and the weighted-Euler
second-complement shear.  Neither operation changes the parameter order: Euler
scaling contributes only a fixed source monomial, and the shear has unit
genuine quotient coefficient.  Thus both the historical active-pivot `+4`
clock and the exact transverse-inflation `+6` clock transport literally to the
straightened full determinant.

This is the full-determinant companion of
`binaryWeightedEulerShear_parameterLayer_profileOrder_eq_zero`.  No active
pivot is divided out here; cancellation remains integral.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **Integral low-order pivot cancellation.**

If `A` has nonzero constant coefficient, then its parameter trailing degree is
zero.  Over a domain, multiplication by `A` therefore cannot hide the first
nonzero coefficient of `B`.  Hence vanishing of all coefficients of `A * B`
through order `N` forces the same vanishing for `B` through order `N`.

This is the exact cancellation principle needed by the R18 Schur closure: it
uses only the nonzero constant active pivot and never inverts that pivot. -/
theorem polynomial_coeff_eq_zero_of_mul_coeff_eq_zero_up_to_of_coeff_zero_ne_zero
    {R : Type*} [CommRing R] [IsDomain R]
    (A B : Polynomial R)
    (hA0 : A.coeff 0 ≠ 0)
    {N n : ℕ}
    (hn : n ≤ N)
    (hprod : ∀ m : ℕ, m ≤ N → (A * B).coeff m = 0) :
    B.coeff n = 0 := by
  by_contra hBn
  have hA : A ≠ 0 := by
    intro hzero
    rw [hzero] at hA0
    simp at hA0
  have hB : B ≠ 0 := by
    intro hzero
    rw [hzero] at hBn
    simp at hBn
  have hAtrail : A.natTrailingDegree = 0 := by
    exact (Polynomial.natTrailingDegree_eq_zero).2 (Or.inr hA0)
  have hBtrail_le : B.natTrailingDegree ≤ n :=
    Polynomial.natTrailingDegree_le_of_ne_zero hBn
  have hmultrail :
      (A * B).natTrailingDegree = B.natTrailingDegree := by
    rw [Polynomial.natTrailingDegree_mul hA hB, hAtrail, zero_add]
  have hmul : A * B ≠ 0 := mul_ne_zero hA hB
  have hcoeff :
      (A * B).coeff (A * B).natTrailingDegree ≠ 0 :=
    (Polynomial.coeff_natTrailingDegree_ne_zero).2 hmul
  rw [hmultrail] at hcoeff
  exact hcoeff (hprod B.natTrailingDegree (le_trans hBtrail_le hn))

/-- Low-order Schur vanishing cancels a nonzero constant active pivot and gives
low-order full-determinant vanishing.  This is just the general integral
cancellation lemma composed with
`schurDetCore = activeDet * determinantCore`. -/
theorem generalFourBlock_determinantCore_coeff_eq_zero_of_schurDetCore_coeff_eq_zero_up_to
    {R : Type*} [CommRing R] [IsDomain R]
    (H : GeneralFourBlock (Polynomial R))
    (hactive0 : H.activeDet.coeff 0 ≠ 0)
    {N n : ℕ}
    (hn : n ≤ N)
    (hschur : ∀ m : ℕ, m ≤ N → H.schurDetCore.coeff m = 0) :
    H.determinantCore.coeff n = 0 := by
  apply polynomial_coeff_eq_zero_of_mul_coeff_eq_zero_up_to_of_coeff_zero_ne_zero
    H.activeDet H.determinantCore hactive0 hn
  intro m hm
  rw [← H.schurDetCore_eq_activeDet_mul_determinantCore]
  exact hschur m hm

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

/-- **R18 inflation-matched straightened determinant clock.**  The exact six
parameter powers contributed by simultaneous transverse inflation are also
strictly before determinant closure, so the corresponding straightened Euler
layer vanishes. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryWeightedEulerShear_determinantCore_parameterLayer_profileOrder_add_six_eq_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4))
    (n : ℕ) :
    familyParameterLayer
        (P.binaryWeightedEulerShear rho).determinantCore
        ((2 * T.topFace.degree - P.profileWeight * n) + 6) = 0 := by
  rw [P.binaryWeightedEulerShear_determinantCore_eq_sourceFactor_mul rho]
  rw [binaryEulerDeterminantSourceFactor_eq_map_C]
  rw [familyParameterLayer_map_C_mul]
  rw [P.binaryHomogenized_permutedSourceDeterminantCore_parameterLayer_profileOrder_add_six_eq_zero
    rho n]
  simp

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
