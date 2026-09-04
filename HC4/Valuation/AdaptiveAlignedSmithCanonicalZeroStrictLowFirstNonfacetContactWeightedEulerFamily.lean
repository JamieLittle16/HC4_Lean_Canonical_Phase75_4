import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactFamilyParameterEuler
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactWeightedEulerHessian
import Mathlib.Tactic

/-!
# A19.R18: family-level weighted Euler/Hessian identities

The coefficientwise contact-Rees Euler identities are already proved on every
source monomial.  The final Schur adapter, however, needs them as identities of
whole polynomial families before applying `GeneralFourBlock` row/column
operations.  The canonical family-level parameter Euler operators now make
that lift literal.

No new support assumption is introduced here: each proof is extensional and
uses the existing support-wide coefficient theorem.  This module is the
family-level interface consumed by the final quotient straightening.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- **R18 family weighted Euler equation.** -/
theorem QsOtherFacetContactQuadraticReesPackage.contactFamily_weightedEuler
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    familyParameterEuler P.contactFamily +
        MvPolynomial.C (Polynomial.C (P.profileWeight : K)) *
          HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily +
      HC4.Polynomial.mvEuler (1 : Fin 4) P.contactFamily +
      HC4.Polynomial.mvEuler (2 : Fin 4) P.contactFamily +
      HC4.Polynomial.mvEuler (3 : Fin 4) P.contactFamily =
    MvPolynomial.C (Polynomial.C (T.topFace.degree : K)) *
      P.contactFamily := by
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    coeff_familyParameterEuler, coeff_mvEuler]
  have h := P.contactFamily_weightedEuler_coeff d
  linear_combination h

/-- **R18 family falling source-row equation.**  This is the whole-family
form of the second-order weighted Euler identity used to straighten the
second complementary Schur direction. -/
theorem QsOtherFacetContactQuadraticReesPackage.contactFamily_fallingWeightedEulerRow
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (i : Fin 4) :
    familyParameterEuler (HC4.Polynomial.mvEuler i P.contactFamily) +
        MvPolynomial.C (Polynomial.C (P.profileWeight : K)) *
          HC4.Polynomial.eulerScaledHessian
            P.contactFamily i (0 : Fin 4) +
      HC4.Polynomial.eulerScaledHessian
        P.contactFamily i (1 : Fin 4) +
      HC4.Polynomial.eulerScaledHessian
        P.contactFamily i (2 : Fin 4) +
      HC4.Polynomial.eulerScaledHessian
        P.contactFamily i (3 : Fin 4) =
    MvPolynomial.C
        (Polynomial.C
          ((T.topFace.degree : K) -
            (if i = (0 : Fin 4) then (P.profileWeight : K) else 1))) *
      HC4.Polynomial.mvEuler i P.contactFamily := by
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    coeff_familyParameterEuler]
  exact P.contactFamily_fallingWeightedEulerRow_coeff i d

/-- **R18 family falling parameter-row equation.** -/
theorem QsOtherFacetContactQuadraticReesPackage.contactFamily_fallingWeightedEulerParameterRow
    (P : QsOtherFacetContactQuadraticReesPackage C) :
    familyParameterSecondEuler P.contactFamily +
        MvPolynomial.C (Polynomial.C (P.profileWeight : K)) *
          familyParameterEuler
            (HC4.Polynomial.mvEuler (0 : Fin 4) P.contactFamily) +
      familyParameterEuler
        (HC4.Polynomial.mvEuler (1 : Fin 4) P.contactFamily) +
      familyParameterEuler
        (HC4.Polynomial.mvEuler (2 : Fin 4) P.contactFamily) +
      familyParameterEuler
        (HC4.Polynomial.mvEuler (3 : Fin 4) P.contactFamily) =
    MvPolynomial.C
        (Polynomial.C ((T.topFace.degree : K) - 1)) *
      familyParameterEuler P.contactFamily := by
  apply MvPolynomial.ext
  intro d
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul,
    coeff_familyParameterEuler, coeff_familyParameterSecondEuler]
  exact P.contactFamily_fallingWeightedEulerParameterRow_coeff d

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
