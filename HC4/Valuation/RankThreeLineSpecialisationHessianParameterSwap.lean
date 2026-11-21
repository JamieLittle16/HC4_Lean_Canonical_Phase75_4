import HC4.Valuation.RankThreeLineSpecialisationParameterSwap
import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerHessianBridge
import HC4.Polynomial.ComplementaryMvSubstitution
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Tactic

/-!
# Parameter/longitudinal swap for Euler-scaled Hessian layers

After rank-three line specialisation a polynomial-parameter source family has
nested coefficient ring `K[τ][X]`.  Swapping the two univariate variables puts
`τ` outside.  The coefficient at outer order `q` should therefore be the
rank-three specialisation of the Euler-scaled Hessian of the honest source
layer `familyParameterLayer P q`.

The only extra bookkeeping beyond the existing parameter-swap theorem is that
exact parameter extraction commutes with multiplication by spatial variables.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial
open scoped Matrix Polynomial.Bivariate

universe u
variable {K : Type u} [Field K]

/-- Exact parameter extraction commutes with multiplication by one spatial
variable. -/
theorem familyParameterLayer_X_mul
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (q : ℕ) (i : Fin 4) :
    familyParameterLayer (MvPolynomial.X i * P) q =
      MvPolynomial.X i * familyParameterLayer P q := by
  classical
  apply MvPolynomial.ext
  intro d
  rw [familyParameterLayer_coeff]
  simp [MvPolynomial.coeff_X_mul', familyParameterLayer_coeff]

/-- The same statement for the two spatial factors in an Euler-scaled Hessian
entry. -/
theorem familyParameterLayer_X_mul_X_mul
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (q : ℕ) (i j : Fin 4) :
    familyParameterLayer
        (MvPolynomial.X i * MvPolynomial.X j * P) q =
      MvPolynomial.X i * MvPolynomial.X j * familyParameterLayer P q := by
  rw [mul_assoc, familyParameterLayer_X_mul, familyParameterLayer_X_mul]
  rw [← mul_assoc]

/-- Exact parameter extraction commutes entrywise with the Euler-scaled
Hessian. -/
theorem familyParameterLayer_eulerScaledHessian_apply
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (q : ℕ) (i j : Fin 4) :
    familyParameterLayer (eulerScaledHessian P i j) q =
      eulerScaledHessian (familyParameterLayer P q) i j := by
  rw [eulerScaledHessian_apply, eulerScaledHessian_apply]
  rw [familyParameterLayer_X_mul_X_mul]
  rw [familyParameterLayer_pderiv, familyParameterLayer_pderiv]

/-- **Euler-Hessian parameter/longitudinal coefficient bridge.**  After line
specialisation and variable swap, outer coefficient `q` is exactly the
specialised Euler-scaled Hessian of the honest parameter layer `q`. -/
theorem coeff_swap_rankThreeLineSpecialisation_eulerScaledHessian
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (q : ℕ) (i j : Fin 4) :
    (Polynomial.Bivariate.swap
      (rankThreeLineSpecialisation (eulerScaledHessian P i j))).coeff q =
      rankThreeLineSpecialisation
        (eulerScaledHessian (familyParameterLayer P q) i j) := by
  rw [coeff_swap_rankThreeLineSpecialisation_eq_parameterLayer]
  rw [familyParameterLayer_eulerScaledHessian_apply]

/-- Matrix-valued swapped specialised Euler Hessian of a source family. -/
noncomputable def swappedRankThreeEulerHessian
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    Matrix (Fin 4) (Fin 4) (Polynomial (Polynomial K)) :=
  fun i j => Polynomial.Bivariate.swap
    (rankThreeLineSpecialisation (eulerScaledHessian P i j))

/-- Coefficients of the swapped specialised matrix are the honest specialised
Euler-Hessian layers. -/
theorem coeff_swappedRankThreeEulerHessian
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (q : ℕ) (i j : Fin 4) :
    (swappedRankThreeEulerHessian P i j).coeff q =
      rankThreeLineSpecialisation
        (eulerScaledHessian (familyParameterLayer P q) i j) := by
  exact coeff_swap_rankThreeLineSpecialisation_eulerScaledHessian P q i j

end

end HC4.Valuation
