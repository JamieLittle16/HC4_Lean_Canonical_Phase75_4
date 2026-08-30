import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactBinaryHomogenization
import Mathlib.Tactic

/-!
# A19.130: exact parameter-Hessian factors of the binary contact family

A19.123 gives every source coefficient of the transversely inflated contact
Rees in the literal form

    tau^(D - r*n) * c_d,

where `n=d₀` and `r=profileWeight`.  This file differentiates that actual
coefficient polynomial, rather than introducing a second abstract binary
family.

After Euler normalisation and evaluation at `tau=1`, the first and second
parameter derivatives are exactly

    (D-r*n) c_d,
    (D-r*n)(D-r*n-1) c_d.

These are the missing parameter-direction factors in the staircase Hessian
coefficient formulas.  The proof keeps natural subtraction honest: on source
support the contact bound proves `r*n <= D`; off support both sides vanish.
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

/-- Every represented-source monomial has enough binary parameter exponent:
`profileWeight * d₀ <= D`. -/
theorem QsOtherFacetContactQuadraticReesPackage.profileWeight_mul_longitudinal_le
    (P : QsOtherFacetContactQuadraticReesPackage C)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ (polynomialFamilySpecialFiber
      T.terminal.blocker.presented.family).support) :
    P.profileWeight * d (0 : Fin 4) ≤ T.topFace.degree := by
  have hbound := P.source_weight_le hd
  have hcoord :
      d (0 : Fin 4) ≤ HC4.Polynomial.ordinaryDegree4 d := by
    simp [HC4.Polynomial.ordinaryDegree4]
  rw [P.profileWeight_eq]
  calc
    (P.contactGap + 1) * d (0 : Fin 4) =
        d (0 : Fin 4) + P.contactGap * d (0 : Fin 4) := by omega
    _ ≤ HC4.Polynomial.ordinaryDegree4 d +
          P.contactGap * d (0 : Fin 4) := Nat.add_le_add_right hcoord _
    _ ≤ T.topFace.degree := hbound

/-- First Euler-normalised parameter derivative of an actual binary-family
source coefficient, evaluated at `tau=1`. -/
theorem QsOtherFacetContactQuadraticReesPackage.eval_one_parameterEuler_coeff_binaryHomogenizedFamily
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.eval 1
        (Polynomial.X * Polynomial.derivative
          (MvPolynomial.coeff d P.binaryHomogenizedFamily)) =
      ((T.topFace.degree : K) -
          (P.profileWeight : K) * (d (0 : Fin 4) : K)) *
        MvPolynomial.coeff d
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  rw [P.coeff_binaryHomogenizedFamily]
  let F := polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  by_cases hd : d ∈ F.support
  · have hle := P.profileWeight_mul_longitudinal_le hd
    have hcast :
        ((T.topFace.degree - P.profileWeight * d (0 : Fin 4) : ℕ) : K) =
          (T.topFace.degree : K) -
            (P.profileWeight : K) * (d (0 : Fin 4) : K) := by
      push_cast
      omega
    rw [Polynomial.derivative_mul]
    simp [hcast]
  · have hcoeff : MvPolynomial.coeff d F = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [F, hcoeff]

/-- Second falling-Euler parameter derivative of an actual binary-family
source coefficient, evaluated at `tau=1`. -/
theorem QsOtherFacetContactQuadraticReesPackage.eval_one_parameterSecondEuler_coeff_binaryHomogenizedFamily
    (P : QsOtherFacetContactQuadraticReesPackage C)
    (d : Fin 4 →₀ ℕ) :
    Polynomial.eval 1
        (Polynomial.X ^ 2 * Polynomial.derivative
          (Polynomial.derivative
            (MvPolynomial.coeff d P.binaryHomogenizedFamily))) =
      (((T.topFace.degree : K) -
          (P.profileWeight : K) * (d (0 : Fin 4) : K)) *
        ((T.topFace.degree : K) -
          (P.profileWeight : K) * (d (0 : Fin 4) : K) - 1)) *
        MvPolynomial.coeff d
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  rw [P.coeff_binaryHomogenizedFamily]
  let F := polynomialFamilySpecialFiber T.terminal.blocker.presented.family
  by_cases hd : d ∈ F.support
  · have hle := P.profileWeight_mul_longitudinal_le hd
    have hcast :
        ((T.topFace.degree - P.profileWeight * d (0 : Fin 4) : ℕ) : K) =
          (T.topFace.degree : K) -
            (P.profileWeight : K) * (d (0 : Fin 4) : K) := by
      push_cast
      omega
    rw [Polynomial.derivative_mul]
    simp [hcast]
    ring
  · have hcoeff : MvPolynomial.coeff d F = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    simp [F, hcoeff]

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
