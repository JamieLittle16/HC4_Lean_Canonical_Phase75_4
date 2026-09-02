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
hypothesis, localization, or cancellation principle.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial
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
  ext d
  rw [coeff_familyParameterEuler, coeff_unitTransverseInflateFamily]
  rw [parameterEuler_X_pow_mul]
  rw [coeff_unitTransverseInflateFamily]
  simp only [MvPolynomial.coeff_add, coeff_familyParameterEuler, coeff_mvEuler]
  have hdeg :
      (pureLongitudinalTransverseDegree d : Polynomial K) =
        (d (1 : Fin 4) : Polynomial K) +
          (d (2 : Fin 4) : Polynomial K) +
          (d (3 : Fin 4) : Polynomial K) := by
    simp [pureLongitudinalTransverseDegree]
  rw [hdeg]
  ring

end

end HC4.Valuation
