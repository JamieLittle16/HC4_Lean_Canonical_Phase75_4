import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryParameterHessianCoefficients
import HC4.Polynomial.ComplementaryMvSubstitution
import Mathlib.Tactic

/-!
# A19.131: mixed and longitudinal Hessian factors of the binary contact family

A19.130 supplies the parameter Euler factors `D-r*n` and
`(D-r*n)(D-r*n-1)` coefficientwise on the honest binary family.  The source
longitudinal direction needs no new geometry: the existing Euler-scaled
Hessian multiplies a monomial by its source exponent, hence contributes `n`
and `n(n-1)`.

This file records that generic coefficient identity once and applies it to the
binary contact family.  Together A19.130 and A19.131 give all three numerical
factors in the R10/R14 staircase Hessian:

    H00 : (D-r*n)(D-r*n-1),
    H01 : n(D-r*n),
    H11 : n(n-1).
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open Polynomial

universe u v

/-- Coefficientwise Euler differentiation of an arbitrary multivariate
polynomial. -/
theorem coeff_mvEuler
    {σ : Type u} {R : Type v} [CommRing R]
    (i : σ) (F : MvPolynomial σ R) (d : σ →₀ ℕ) :
    MvPolynomial.coeff d (MvPolynomial.X i * MvPolynomial.pderiv i F) =
      ((d i : ℕ) : R) * MvPolynomial.coeff d F := by
  classical
  induction F using MvPolynomial.induction_on' with
  | add P Q hP hQ =>
      simp only [map_add, mul_add, MvPolynomial.coeff_add, hP, hQ]
      ring
  | monomial n a =>
      rw [MvPolynomial.X_mul_pderiv_monomial]
      rw [MvPolynomial.coeff_smul]
      by_cases hdn : d = n
      · subst d
        simp [MvPolynomial.coeff_monomial, nsmul_eq_mul]
      · have hnd : n ≠ d := Ne.symm hdn
        simp [MvPolynomial.coeff_monomial, hdn, hnd, nsmul_eq_mul]

/-- Coefficientwise form of the Euler-scaled Hessian. -/
theorem coeff_eulerScaledHessian
    {R : Type v} [CommRing R]
    (F : MvPolynomial (Fin 4) R) (i j : Fin 4) (d : Fin 4 →₀ ℕ) :
    MvPolynomial.coeff d (HC4.Polynomial.eulerScaledHessian F i j) =
      ((((d i : ℕ) : R) * ((d j : ℕ) : R)) -
        if i = j then ((d i : ℕ) : R) else 0) *
        MvPolynomial.coeff d F := by
  by_cases hij : i = j
  · subst j
    change
      MvPolynomial.coeff d
          ((MvPolynomial.X i * MvPolynomial.pderiv i
              (MvPolynomial.X i * MvPolynomial.pderiv i F)) -
            (MvPolynomial.X i * MvPolynomial.pderiv i F)) = _
    rw [MvPolynomial.coeff_sub, coeff_mvEuler, coeff_mvEuler, coeff_mvEuler]
    simp only [if_pos]
    ring
  · change
      MvPolynomial.coeff d
          ((MvPolynomial.X i * MvPolynomial.pderiv i
              (MvPolynomial.X j * MvPolynomial.pderiv j F)) - 0) = _
    rw [MvPolynomial.coeff_sub, MvPolynomial.coeff_zero, sub_zero,
      coeff_mvEuler, coeff_mvEuler]
    simp only [if_neg hij]
    ring

universe w
variable {K : Type w} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- Evaluation at `tau=1` recovers the represented-source coefficient from
the binary homogenized family. -/
theorem QsOtherFacetContactQuadraticReesPackage.eval_one_coeff_binaryHomogenizedFamily
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.eval 1 (MvPolynomial.coeff d P.binaryHomogenizedFamily) =
      MvPolynomial.coeff d
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  rw [P.coeff_binaryHomogenizedFamily]
  simp

/-- Mixed parameter/longitudinal Euler coefficient of the honest binary
family. -/
theorem QsOtherFacetContactQuadraticReesPackage.eval_one_parameterEuler_coeff_longitudinalEuler_binaryHomogenizedFamily
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.eval 1
        (Polynomial.X * Polynomial.derivative
          (MvPolynomial.coeff d
            (HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily))) =
      (d (0 : Fin 4) : K) *
        ((T.topFace.degree : K) -
          (P.profileWeight : K) * (d (0 : Fin 4) : K)) *
        MvPolynomial.coeff d
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  calc
    Polynomial.eval 1
        (Polynomial.X * Polynomial.derivative
          (MvPolynomial.coeff d
            (HC4.Polynomial.mvEuler (0 : Fin 4) P.binaryHomogenizedFamily))) =
      (d (0 : Fin 4) : K) *
        Polynomial.eval 1
          (Polynomial.X * Polynomial.derivative
            (MvPolynomial.coeff d P.binaryHomogenizedFamily)) := by
      rw [HC4.Polynomial.mvEuler, coeff_mvEuler]
      simp [Polynomial.derivative_mul]
    _ = (d (0 : Fin 4) : K) *
        ((T.topFace.degree : K) -
          (P.profileWeight : K) * (d (0 : Fin 4) : K)) *
        MvPolynomial.coeff d
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
      rw [P.eval_one_parameterEuler_coeff_binaryHomogenizedFamily]
      ring

/-- Pure longitudinal falling-Euler Hessian coefficient of the honest binary
family, evaluated at `tau=1`. -/
theorem QsOtherFacetContactQuadraticReesPackage.eval_one_coeff_longitudinalEulerHessian_binaryHomogenizedFamily
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.eval 1
        (MvPolynomial.coeff d
          (HC4.Polynomial.eulerScaledHessian P.binaryHomogenizedFamily
            (0 : Fin 4) 0)) =
      (d (0 : Fin 4) : K) * ((d (0 : Fin 4) : K) - 1) *
        MvPolynomial.coeff d
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  rw [coeff_eulerScaledHessian]
  simp only [if_pos]
  rw [Polynomial.eval_mul]
  rw [P.eval_one_coeff_binaryHomogenizedFamily]
  simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_natCast]
  ring

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
