import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactQuadraticRees
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryLongitudinalHessianCoefficients
import Mathlib.Tactic

/-!
# A19.R18: support-wide weighted Euler identity for the honest contact Rees

The final other-facet Schur adapter must not promote the endpoint arithmetic of
A19.102 to the whole represented source.  The support-wide identity it needs is
already built into the honest reverse-Rees family itself.

For a source exponent `d`, the contact family has parameter exponent

    D - ((r+1)d₀ + d₁ + d₂ + d₃).

Consequently its coefficient satisfies the exact Euler equation

    tau q_d' + ((r+1)d₀ + d₁ + d₂ + d₃) q_d = D q_d.

This file records that identity directly from the reverse-Rees coefficient
formula, together with the corresponding first/second parameter-Hessian
coefficients.  The statements are valid on every source coefficient, including
off-support coefficients, and introduce no homogeneity assumption on the
represented source.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open Polynomial

private theorem parameterEuler_X_pow_mul_C
    {R : Type*} [CommRing R] (n : ℕ) (a : R) :
    Polynomial.X * Polynomial.derivative
        ((Polynomial.X : Polynomial R) ^ n * Polynomial.C a) =
      Polynomial.C (n : R) *
        ((Polynomial.X : Polynomial R) ^ n * Polynomial.C a) := by
  rw [Polynomial.derivative_mul, Polynomial.derivative_C]
  simp only [mul_zero, add_zero]
  cases n with
  | zero => simp
  | succ n =>
      rw [Polynomial.derivative_X_pow_succ]
      rw [pow_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

private theorem parameterSecondEuler_X_pow_mul_C
    {R : Type*} [CommRing R] (n : ℕ) (a : R) :
    Polynomial.X ^ 2 * Polynomial.derivative
        (Polynomial.derivative
          ((Polynomial.X : Polynomial R) ^ n * Polynomial.C a)) =
      Polynomial.C ((n : R) * ((n : R) - 1)) *
        ((Polynomial.X : Polynomial R) ^ n * Polynomial.C a) := by
  rw [Polynomial.derivative_mul, Polynomial.derivative_C]
  simp only [mul_zero, add_zero]
  rw [Polynomial.derivative_mul, Polynomial.derivative_C]
  simp only [mul_zero, add_zero]
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero => simp
      | succ n =>
          rw [Polynomial.derivative_X_pow_succ]
          rw [Polynomial.derivative_mul, Polynomial.derivative_C]
          simp only [zero_mul, zero_add]
          rw [Polynomial.derivative_X_pow_succ]
          simp only [Nat.cast_add, Nat.cast_one]
          rw [pow_succ, pow_succ]
          ring_nf

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- Parameter-Euler eigenvalue of every coefficient of the honest contact
reverse Rees, stated first in the native contact weight. -/
theorem QsOtherFacetContactQuadraticReesPackage.contactFamily_parameterEuler_coeff_weight
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.X * Polynomial.derivative
        (MvPolynomial.coeff d P.contactFamily) =
      Polynomial.C
          ((T.topFace.degree : K) -
            (Finsupp.weight (qsIntegralContactWeight P.contactGap) d : K)) *
        MvPolynomial.coeff d P.contactFamily := by
  rw [QsOtherFacetContactQuadraticReesPackage.contactFamily]
  rw [reverseWeightedReesFamily_coeff]
  by_cases hd : d ∈ (polynomialFamilySpecialFiber
      T.terminal.blocker.presented.family).support
  · rw [if_pos hd]
    have hle := P.bound d hd
    have hcast :
        ((T.topFace.degree -
            Finsupp.weight (qsIntegralContactWeight P.contactGap) d : ℕ) : K) =
          (T.topFace.degree : K) -
            (Finsupp.weight (qsIntegralContactWeight P.contactGap) d : K) := by
      rw [Nat.cast_sub hle]
    rw [parameterEuler_X_pow_mul_C]
    rw [hcast]
  · rw [if_neg hd]
    simp

/-- The native contact weight is exactly the binary longitudinal profile
weight plus the three unit transverse weights. -/
theorem QsOtherFacetContactQuadraticReesPackage.contactFamily_parameterEuler_coeff
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.X * Polynomial.derivative
        (MvPolynomial.coeff d P.contactFamily) =
      Polynomial.C
          ((T.topFace.degree : K) -
            ((P.profileWeight : K) * (d (0 : Fin 4) : K) +
              (d (1 : Fin 4) : K) + (d (2 : Fin 4) : K) +
              (d (3 : Fin 4) : K))) *
        MvPolynomial.coeff d P.contactFamily := by
  rw [P.contactFamily_parameterEuler_coeff_weight d]
  congr 2
  rw [qsIntegralContactWeight_finsupp, P.profileWeight_eq]
  simp only [HC4.Polynomial.ordinaryDegree4]
  push_cast
  ring

/-- **R18 support-wide weighted Euler equation.**  This is the legitimate
replacement for any attempt to extend A19.102's endpoint relation to all
source monomials. -/
theorem QsOtherFacetContactQuadraticReesPackage.contactFamily_weightedEuler_coeff
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.X * Polynomial.derivative
        (MvPolynomial.coeff d P.contactFamily) +
      Polynomial.C
          ((P.profileWeight : K) * (d (0 : Fin 4) : K) +
            (d (1 : Fin 4) : K) + (d (2 : Fin 4) : K) +
            (d (3 : Fin 4) : K)) *
        MvPolynomial.coeff d P.contactFamily =
      Polynomial.C (T.topFace.degree : K) *
        MvPolynomial.coeff d P.contactFamily := by
  rw [P.contactFamily_parameterEuler_coeff d]
  let w : K :=
    (P.profileWeight : K) * (d (0 : Fin 4) : K) +
      (d (1 : Fin 4) : K) + (d (2 : Fin 4) : K) +
      (d (3 : Fin 4) : K)
  let q : Polynomial K := MvPolynomial.coeff d P.contactFamily
  change Polynomial.C ((T.topFace.degree : K) - w) * q +
      Polynomial.C w * q = Polynomial.C (T.topFace.degree : K) * q
  rw [← add_mul, ← Polynomial.C_add, sub_add_cancel]

/-- Exact second falling parameter-Euler coefficient of the honest contact
family, in the native contact weight. -/
theorem QsOtherFacetContactQuadraticReesPackage.contactFamily_parameterSecondEuler_coeff_weight
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.X ^ 2 * Polynomial.derivative
        (Polynomial.derivative (MvPolynomial.coeff d P.contactFamily)) =
      Polynomial.C
          (((T.topFace.degree : K) -
              (Finsupp.weight (qsIntegralContactWeight P.contactGap) d : K)) *
            ((T.topFace.degree : K) -
              (Finsupp.weight (qsIntegralContactWeight P.contactGap) d : K) - 1)) *
        MvPolynomial.coeff d P.contactFamily := by
  rw [QsOtherFacetContactQuadraticReesPackage.contactFamily]
  rw [reverseWeightedReesFamily_coeff]
  by_cases hd : d ∈ (polynomialFamilySpecialFiber
      T.terminal.blocker.presented.family).support
  · rw [if_pos hd]
    have hle := P.bound d hd
    have hcast :
        ((T.topFace.degree -
            Finsupp.weight (qsIntegralContactWeight P.contactGap) d : ℕ) : K) =
          (T.topFace.degree : K) -
            (Finsupp.weight (qsIntegralContactWeight P.contactGap) d : K) := by
      rw [Nat.cast_sub hle]
    rw [parameterSecondEuler_X_pow_mul_C]
    rw [hcast]
  · rw [if_neg hd]
    simp

/-- Expanded second parameter-Euler coefficient. -/
theorem QsOtherFacetContactQuadraticReesPackage.contactFamily_parameterSecondEuler_coeff
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.X ^ 2 * Polynomial.derivative
        (Polynomial.derivative (MvPolynomial.coeff d P.contactFamily)) =
      Polynomial.C
          (((T.topFace.degree : K) -
              ((P.profileWeight : K) * (d (0 : Fin 4) : K) +
                (d (1 : Fin 4) : K) + (d (2 : Fin 4) : K) +
                (d (3 : Fin 4) : K))) *
            ((T.topFace.degree : K) -
              ((P.profileWeight : K) * (d (0 : Fin 4) : K) +
                (d (1 : Fin 4) : K) + (d (2 : Fin 4) : K) +
                (d (3 : Fin 4) : K)) - 1)) *
        MvPolynomial.coeff d P.contactFamily := by
  rw [P.contactFamily_parameterSecondEuler_coeff_weight d]
  congr 2
  rw [qsIntegralContactWeight_finsupp, P.profileWeight_eq]
  simp only [HC4.Polynomial.ordinaryDegree4]
  push_cast
  ring

/-- Mixed parameter/source Euler coefficient for every source direction. -/
theorem QsOtherFacetContactQuadraticReesPackage.contactFamily_parameterEuler_sourceEuler_coeff
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (i : Fin 4) (d : Fin 4 →₀ ℕ) :
    Polynomial.X * Polynomial.derivative
        (MvPolynomial.coeff d (HC4.Polynomial.mvEuler i P.contactFamily)) =
      (d i : Polynomial K) *
        Polynomial.C
          ((T.topFace.degree : K) -
            ((P.profileWeight : K) * (d (0 : Fin 4) : K) +
              (d (1 : Fin 4) : K) + (d (2 : Fin 4) : K) +
              (d (3 : Fin 4) : K))) *
        MvPolynomial.coeff d P.contactFamily := by
  rw [coeff_mvEuler]
  simp only [Polynomial.derivative_mul]
  have hconst : Polynomial.derivative (d i : Polynomial K) = 0 := by simp
  rw [hconst, zero_mul, zero_add]
  calc
    Polynomial.X *
          ((d i : Polynomial K) *
            Polynomial.derivative (MvPolynomial.coeff d P.contactFamily)) =
        (d i : Polynomial K) *
          (Polynomial.X *
            Polynomial.derivative (MvPolynomial.coeff d P.contactFamily)) := by
      ring
    _ = (d i : Polynomial K) *
          (Polynomial.C
              ((T.topFace.degree : K) -
                ((P.profileWeight : K) * (d (0 : Fin 4) : K) +
                  (d (1 : Fin 4) : K) + (d (2 : Fin 4) : K) +
                  (d (3 : Fin 4) : K))) *
            MvPolynomial.coeff d P.contactFamily) := by
      rw [P.contactFamily_parameterEuler_coeff d]
    _ = _ := by ring

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
