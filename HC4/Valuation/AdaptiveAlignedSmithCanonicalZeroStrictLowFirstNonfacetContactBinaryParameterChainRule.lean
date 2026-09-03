import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryEulerSchurTransport
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFamilyParameterEuler
import Mathlib.Tactic

/-!
# A19.R18: parameter chain rule for the binary transverse inflation

The binary contact family is obtained from the honest contact Rees by the
simultaneous substitution

    x₁ ↦ τ x₁,  x₂ ↦ τ x₂,  x₃ ↦ τ x₃.

Consequently `τ ∂τ` on the inflated family is the inflation of the original
parameter Euler operator plus the three transverse source Euler operators.
This is the exact family-level bridge needed to turn the contact weighted-Euler
straightening into the binary parameter/longitudinal Hessian calculation.

The statement is representation plumbing only.  It uses the existing combined
inflation and parameter-Euler owners and introduces no new geometric
hypothesis, localization, or cancellation principle.  The identity is stated
at whole-family level so the final Schur adapter can consume it directly, and
the downstream profile-determinant extraction remains a literal coefficient
calculation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K]

private theorem parameterEuler_X_pow_mul
    (m : ℕ) (c : Polynomial K) :
    Polynomial.X * Polynomial.derivative
        ((Polynomial.X : Polynomial K) ^ m * c) =
      (Polynomial.X : Polynomial K) ^ m *
        (Polynomial.X * Polynomial.derivative c +
          (m : Polynomial K) * c) := by
  cases m with
  | zero => simp
  | succ m =>
      rw [Polynomial.derivative_mul, Polynomial.derivative_X_pow_succ]
      rw [pow_succ]
      push_cast
      have hnat :
          (m : Polynomial K) = Polynomial.C (m : K) := by
        exact (map_natCast (Polynomial.C : K →+* Polynomial K) m).symm
      rw [hnat]
      simp only [map_add, map_one]
      ring

/-- **R18 transverse-inflation parameter chain rule.**  Parameter Euler after
simultaneous unit transverse inflation equals the inflated sum of the old
parameter Euler direction and the three transverse source Euler directions. -/
theorem familyParameterEuler_unitTransverseInflateFamily
    (F : MvPolynomial (Fin 4) (Polynomial K)) :
    familyParameterEuler (unitTransverseInflateFamily (K := K) F) =
      unitTransverseInflateFamily (K := K)
        (familyParameterEuler F +
          HC4.Polynomial.mvEuler (1 : Fin 4) F +
          HC4.Polynomial.mvEuler (2 : Fin 4) F +
          HC4.Polynomial.mvEuler (3 : Fin 4) F) := by
  apply MvPolynomial.ext
  intro d
  rw [coeff_familyParameterEuler, coeff_unitTransverseInflateFamily]
  rw [parameterEuler_X_pow_mul]
  rw [coeff_unitTransverseInflateFamily]
  simp only [MvPolynomial.coeff_add, coeff_familyParameterEuler, coeff_mvEuler]
  have hdeg :
      ((d (1 : Fin 4) + d (2 : Fin 4) + d (3 : Fin 4) : ℕ) : Polynomial K) =
        (d (1 : Fin 4) : Polynomial K) +
          (d (2 : Fin 4) : Polynomial K) +
          (d (3 : Fin 4) : Polynomial K) := by
    push_cast
    ring
  rw [hdeg]
  ring

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable [CharZero K] [IsAlgClosed K]
variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- **R18 binary weighted Euler equation.**  After the three transverse
inflations, the transverse grading has moved entirely into the family
parameter, leaving the literal two-variable weight `(1, profileWeight)` on
`(tau, x₀)`. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryHomogenized_weightedEuler
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    familyParameterEuler P.binaryHomogenizedFamily +
        MvPolynomial.C (Polynomial.C (P.profileWeight : K)) *
          HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily =
      MvPolynomial.C (Polynomial.C (T.topFace.degree : K)) *
        P.binaryHomogenizedFamily := by
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    coeff_familyParameterEuler, coeff_mvEuler]
  rw [P.parameterEuler_coeff_binaryHomogenizedFamily d]
  simp only [map_sub, map_mul, map_natCast, map_one]
  ring

/-- **R18 binary falling parameter row.**  Differentiating the two-variable
weighted Euler equation in the family parameter gives the exact relation among
`H00` and `H01` used by the profile Hessian. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryHomogenized_fallingParameterRow
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    familyParameterSecondEuler P.binaryHomogenizedFamily +
        MvPolynomial.C (Polynomial.C (P.profileWeight : K)) *
          familyParameterEuler
            (HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily) =
      MvPolynomial.C
          (Polynomial.C ((T.topFace.degree : K) - 1)) *
        familyParameterEuler P.binaryHomogenizedFamily := by
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    coeff_familyParameterSecondEuler, coeff_familyParameterEuler]
  rw [P.parameterSecondEuler_coeff_binaryHomogenizedFamily d]
  rw [P.parameterEuler_longitudinalEuler_coeff_binaryHomogenizedFamily d]
  rw [P.parameterEuler_coeff_binaryHomogenizedFamily d]
  simp only [map_sub, map_add, map_mul, map_pow, map_neg,
    map_natCast, map_one]
  ring

/-- **R18 binary falling longitudinal row.**  Differentiating in `x₀` gives
the exact relation among the mixed and longitudinal entries of the canonical
binary profile Hessian. -/
theorem QsOtherFacetContactQuadraticReesPackage.binaryHomogenized_fallingLongitudinalRow
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    familyParameterEuler
        (HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily) +
        MvPolynomial.C (Polynomial.C (P.profileWeight : K)) *
          HC4.Polynomial.eulerScaledHessian
            P.binaryHomogenizedFamily (0 : Fin 4) (0 : Fin 4) =
      MvPolynomial.C
          (Polynomial.C
            ((T.topFace.degree : K) - (P.profileWeight : K))) *
        HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily := by
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    coeff_familyParameterEuler, coeff_mvEuler]
  rw [P.parameterEuler_longitudinalEuler_coeff_binaryHomogenizedFamily d]
  rw [P.longitudinalEulerHessian_coeff_binaryHomogenizedFamily d]
  simp only [map_sub, map_add, map_mul, map_pow, map_natCast, map_one]
  ring

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation