import HC4.Valuation.ParameterFirstLayerBridge
import Mathlib.Tactic

/-!
# A19.R18: family-level parameter Euler operators

The final contact/Schur adapter needs to use the parameter Euler direction as
an honest family operation, not only coefficient by coefficient.  The project
already owns the canonical `parameterFirstEquiv`, which moves the coefficient
parameter to the outer polynomial variable.  We therefore define the first
and falling second parameter-Euler operators by conjugating the ordinary
univariate operators through that equivalence.

Their exact source layers are immediate: layer `n` is multiplied by `n` and
`n(n-1)` respectively.  This is representation plumbing only; no new contact
geometry, homogeneity hypothesis, or cancellation principle is introduced.
-/

namespace HC4.Valuation

noncomputable section

open Polynomial

universe u
variable {K : Type u} [Field K]

/-- The family-level Euler operator in the coefficient parameter, `τ ∂τ`. -/
noncomputable def familyParameterEuler
    (F : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  (parameterFirstEquiv K).symm
    (Polynomial.X * Polynomial.derivative (parameterFirstEquiv K F))

/-- The family-level falling second parameter-Euler operator, `τ² ∂τ²`. -/
noncomputable def familyParameterSecondEuler
    (F : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  (parameterFirstEquiv K).symm
    (Polynomial.X ^ 2 *
      Polynomial.derivative (Polynomial.derivative (parameterFirstEquiv K F)))

@[simp]
theorem parameterFirstEquiv_familyParameterEuler
    (F : MvPolynomial (Fin 4) (Polynomial K)) :
    parameterFirstEquiv K (familyParameterEuler F) =
      Polynomial.X * Polynomial.derivative (parameterFirstEquiv K F) := by
  simp [familyParameterEuler]

@[simp]
theorem parameterFirstEquiv_familyParameterSecondEuler
    (F : MvPolynomial (Fin 4) (Polynomial K)) :
    parameterFirstEquiv K (familyParameterSecondEuler F) =
      Polynomial.X ^ 2 *
        Polynomial.derivative (Polynomial.derivative (parameterFirstEquiv K F)) := by
  simp [familyParameterSecondEuler]

/-- Exact layer formula for `τ ∂τ`. -/
theorem familyParameterLayer_familyParameterEuler
    (F : MvPolynomial (Fin 4) (Polynomial K)) (n : ℕ) :
    familyParameterLayer (familyParameterEuler F) n =
      (n : MvPolynomial (Fin 4) K) * familyParameterLayer F n := by
  rw [← parameterFirstEquiv_coeff, ← parameterFirstEquiv_coeff]
  rw [parameterFirstEquiv_familyParameterEuler]
  cases n with
  | zero => simp
  | succ n =>
      simp only [Nat.succ_eq_add_one, Polynomial.coeff_X_mul,
        Polynomial.coeff_derivative]
      push_cast
      ring

/-- Exact layer formula for `τ² ∂τ²`. -/
theorem familyParameterLayer_familyParameterSecondEuler
    (F : MvPolynomial (Fin 4) (Polynomial K)) (n : ℕ) :
    familyParameterLayer (familyParameterSecondEuler F) n =
      (n : MvPolynomial (Fin 4) K) *
        ((n : MvPolynomial (Fin 4) K) - 1) * familyParameterLayer F n := by
  rw [← parameterFirstEquiv_coeff, ← parameterFirstEquiv_coeff]
  rw [parameterFirstEquiv_familyParameterSecondEuler]
  cases n with
  | zero => simp
  | succ n =>
      cases n with
      | zero => simp
      | succ n =>
          simp only [pow_two, Nat.succ_eq_add_one, Polynomial.coeff_X_mul,
            Polynomial.coeff_derivative]
          push_cast
          ring

end

end HC4.Valuation
