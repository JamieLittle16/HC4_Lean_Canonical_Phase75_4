import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryDeterminantInflation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinarySourceSchurClock
import Mathlib.Tactic

/-!
# A19.R18: cancel the exact binary determinant inflation shift

The binary contact family is obtained from the honest contact Rees by one
simultaneous transverse inflation in source coordinates `1,2,3`.  The ordinary
four-by-four Hessian determinant therefore carries exactly six powers of the
parameter.  R20/R18 already proves that the binary determinant layer at the
profile order shifted by those six powers is zero.

This module performs that cancellation literally at the level of exact
parameter layers.  No active pivot is inverted, no localization is introduced,
and no new geometric or homogeneity hypothesis is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Removing an explicit parameter monomial from an exact parameter layer just
shifts the requested layer by its exponent. -/
theorem familyParameterLayer_C_X_pow_mul_add
    (F : MvPolynomial (Fin 4) (Polynomial K))
    (s n : ℕ) :
    familyParameterLayer
        ((MvPolynomial.C (Polynomial.X : Polynomial K)) ^ s * F)
        (n + s) =
      familyParameterLayer F n := by
  rw [← MvPolynomial.C_pow]
  ext d
  rw [familyParameterLayer_coeff, MvPolynomial.coeff_C_mul,
    familyParameterLayer_coeff]
  rw [Polynomial.coeff_X_pow_mul']
  have hle : s ≤ n + s := by omega
  simp [hle]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- **R18 exact determinant-inflation cancellation.**  After removing the six
parameter powers contributed by simultaneous transverse inflation, the
inflated honest-contact determinant has zero layer at every binary staircase
profile order.

This is the direct consumer of the `+6` determinant clock and the exact
`tau^6` determinant covariance. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryInflatedContactDeterminantCore_parameterLayer_profileOrder_eq_zero
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (rho : Equiv.Perm (Fin 4))
    (hzero : rho 0 ≠ 0)
    (hone : rho 1 ≠ 0)
    (htwo : rho 2 = 0)
    (hthree : rho 3 ≠ 0)
    (n : ℕ) :
    familyParameterLayer
        (unitTransverseInflateFamily (K := K)
          (permutedPolynomialHessianFourBlock rho P.contactFamily).determinantCore)
        (2 * T.topFace.degree - P.profileWeight * n) = 0 := by
  have h :=
    P.binaryHomogenized_permutedSourceDeterminantCore_parameterLayer_profileOrder_add_six_eq_zero
      rho n
  rw [QsOtherFacetContactQuadraticReesPackage.binaryHomogenizedFamily] at h
  rw [permutedPolynomialHessianFourBlock_determinantCore_unitTransverseInflateFamily
    rho P.contactFamily hzero hone htwo hthree] at h
  rw [familyParameterLayer_C_X_pow_mul_add] at h
  exact h

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
