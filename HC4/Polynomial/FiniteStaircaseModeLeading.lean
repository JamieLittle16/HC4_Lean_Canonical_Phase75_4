import HC4.Polynomial.FiniteStaircasePureModeMomentLeading
import Mathlib.Tactic

/-!
# Leading longitudinal mode of an arbitrary staircase profile

The final one-fibre source profile is not itself assumed to be a monomial in
the original longitudinal coordinate.  What matters for the mixed determinant
coefficient is only its top longitudinal coefficient.

On the upper diagonal `j=k`, the coefficient of `X^k` in the staircase moment
matrix is the scalar `phi_k` times the exponent core `(k,0,1,Vk)`.  On the
lower diagonal `j+2=k`, the coefficient of `X^(k-1)` is `phi_(k-1)` times the
core `(k-1,1,0,V(k-1))`.

These are direct instances of the generic affine-moment coefficient formula.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Upper diagonal `j=k`: exact coefficient matrix at longitudinal degree
`k`, for an arbitrary coefficient profile. -/
theorem coeff_upperMode_parallelStaircase
    (V k : ℕ) (phi : Polynomial K) :
    (fun r s =>
      (parallelStaircaseMomentHessian V k k phi r s).coeff k) =
      phi.coeff k • fieldExponentHessianCore
        ![(k : K), 0, 1, (V : K) * (k : K)] := by
  apply Matrix.ext
  intro r s
  rw [coeff_rankThreeAffinePolynomialMomentHessian]
  fin_cases r <;> fin_cases s <;>
    simp [parallelStaircaseMomentHessian, fieldExponentHessianCore,
      rankThreeLogBaseExponent, rankThreeLogDirection] <;>
    push_cast <;> ring

/-- Lower diagonal `j+2=k`: exact coefficient matrix at longitudinal degree
`k-1`, again for an arbitrary profile. -/
theorem coeff_lowerMode_parallelStaircase
    (V k : ℕ) (hk : 2 ≤ k) (phi : Polynomial K) :
    (fun r s =>
      (parallelStaircaseMomentHessian V k (k - 2) phi r s).coeff (k - 1)) =
      phi.coeff (k - 1) • fieldExponentHessianCore
        ![((k - 1 : ℕ) : K), 1, 0,
          (V : K) * ((k - 1 : ℕ) : K)] := by
  apply Matrix.ext
  intro r s
  rw [coeff_rankThreeAffinePolynomialMomentHessian]
  have hk1 : k - 1 ≤ k := by omega
  have hk2 : k - 1 ≤ (k - 2) + 1 := by omega
  have hk3 : k - 1 ≤ k + (k - 2) := by omega
  rw [Nat.cast_sub hk1, Nat.cast_sub hk2, Nat.cast_sub hk3]
  fin_cases r <;> fin_cases s <;>
    simp [parallelStaircaseMomentHessian, fieldExponentHessianCore,
      rankThreeLogBaseExponent, rankThreeLogDirection] <;>
    push_cast <;> ring

end

end HC4.Polynomial
