import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryParameterHessianCoefficients
import Mathlib.Tactic

/-!
# A19.132: exact binary Euler identities over the parameter ring

A19.130 records the parameter-Hessian factors after evaluating `tau=1`, which
is the form eventually consumed by the fraction-field profile.  The Schur
series comparison needs the stronger pre-evaluation statement.

For every actual source coefficient `q_d(tau)` of the binary contact family,
A19.123 gives

    q_d(tau) = tau^(D-r*n) c_d,   n=d₀.

Hence, in the parameter polynomial ring itself,

    tau q_d' = (D-r*n) q_d,
    tau^2 q_d'' = (D-r*n)(D-r*n-1) q_d.

The support/off-support split is the same honest natural-subtraction argument
already certified in A19.130.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open Polynomial

private theorem parameterEuler_X_pow
    {R : Type*} [CommRing R] (n : ℕ) :
    Polynomial.X * Polynomial.derivative
        ((Polynomial.X : Polynomial R) ^ n) =
      Polynomial.C (n : R) * Polynomial.X ^ n := by
  cases n with
  | zero => simp
  | succ n =>
      rw [Polynomial.derivative_X_pow_succ]
      rw [pow_succ]
      simp only [Nat.cast_add, Nat.cast_one]
      ring

private theorem parameterSecondEuler_X_pow
    {R : Type*} [CommRing R] (n : ℕ) :
    Polynomial.X ^ 2 * Polynomial.derivative
        (Polynomial.derivative ((Polynomial.X : Polynomial R) ^ n)) =
      Polynomial.C ((n : R) * ((n : R) - 1)) * Polynomial.X ^ n := by
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero => simp
      | succ n =>
          rw [Polynomial.derivative_X_pow_succ]
          rw [Polynomial.derivative_C_mul]
          rw [Polynomial.derivative_X_pow_succ]
          simp only [Nat.cast_add, Nat.cast_one]
          rw [pow_succ, pow_succ]
          ring_nf

private theorem parameterEuler_X_pow_mul_C
    {R : Type*} [CommRing R] (n : ℕ) (a : R) :
    Polynomial.X * Polynomial.derivative
        ((Polynomial.X : Polynomial R) ^ n * Polynomial.C a) =
      Polynomial.C (n : R) *
        ((Polynomial.X : Polynomial R) ^ n * Polynomial.C a) := by
  rw [Polynomial.derivative_mul, Polynomial.derivative_C]
  simp only [mul_zero, add_zero]
  calc
    Polynomial.X *
        (Polynomial.derivative ((Polynomial.X : Polynomial R) ^ n) *
          Polynomial.C a) =
      (Polynomial.X *
        Polynomial.derivative ((Polynomial.X : Polynomial R) ^ n)) *
          Polynomial.C a := by ring
    _ = Polynomial.C (n : R) *
        ((Polynomial.X : Polynomial R) ^ n * Polynomial.C a) := by
      rw [parameterEuler_X_pow]
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
  calc
    Polynomial.X ^ 2 *
        (Polynomial.derivative
          (Polynomial.derivative ((Polynomial.X : Polynomial R) ^ n)) *
            Polynomial.C a) =
      (Polynomial.X ^ 2 * Polynomial.derivative
        (Polynomial.derivative ((Polynomial.X : Polynomial R) ^ n))) *
          Polynomial.C a := by ring
    _ = Polynomial.C ((n : R) * ((n : R) - 1)) *
        ((Polynomial.X : Polynomial R) ^ n * Polynomial.C a) := by
      rw [parameterSecondEuler_X_pow]
      ring

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
  T .qs}

/-- Exact parameter-Euler eigenvalue of each binary-family source
coefficient. -/
theorem QsOtherFacetContactQuadraticReesPackage.parameterEuler_coeff_binaryHomogenizedFamily
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.X * Polynomial.derivative
        (MvPolynomial.coeff d P.binaryHomogenizedFamily) =
      Polynomial.C
          ((T.topFace.degree : K) -
            (P.profileWeight : K) * (d (0 : Fin 4) : K)) *
        MvPolynomial.coeff d P.binaryHomogenizedFamily := by
  rw [P.coeff_binaryHomogenizedFamily]
  let F := polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  by_cases hd : d ∈ F.support
  · have hle := P.profileWeight_mul_longitudinal_le hd
    have hcast :
        ((T.topFace.degree - P.profileWeight * d (0 : Fin 4) : ℕ) : K) =
          (T.topFace.degree : K) -
            (P.profileWeight : K) * (d (0 : Fin 4) : K) := by
      rw [Nat.cast_sub hle, Nat.cast_mul]
    rw [parameterEuler_X_pow_mul_C]
    rw [hcast]
  · have hcoeff : MvPolynomial.coeff d F = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [F, hcoeff]

/-- Exact second falling-Euler eigenvalue of each binary-family source
coefficient. -/
theorem QsOtherFacetContactQuadraticReesPackage.parameterSecondEuler_coeff_binaryHomogenizedFamily
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.X ^ 2 * Polynomial.derivative
        (Polynomial.derivative
          (MvPolynomial.coeff d P.binaryHomogenizedFamily)) =
      Polynomial.C
          (((T.topFace.degree : K) -
              (P.profileWeight : K) * (d (0 : Fin 4) : K)) *
            ((T.topFace.degree : K) -
              (P.profileWeight : K) * (d (0 : Fin 4) : K) - 1)) *
        MvPolynomial.coeff d P.binaryHomogenizedFamily := by
  rw [P.coeff_binaryHomogenizedFamily]
  let F := polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  by_cases hd : d ∈ F.support
  · have hle := P.profileWeight_mul_longitudinal_le hd
    have hcast :
        ((T.topFace.degree - P.profileWeight * d (0 : Fin 4) : ℕ) : K) =
          (T.topFace.degree : K) -
            (P.profileWeight : K) * (d (0 : Fin 4) : K) := by
      rw [Nat.cast_sub hle, Nat.cast_mul]
    rw [parameterSecondEuler_X_pow_mul_C]
    rw [hcast]
  · have hcoeff : MvPolynomial.coeff d F = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [F, hcoeff]

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
