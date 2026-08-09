import HC4.Polynomial.FourExponent
import HC4.Polynomial.HessianDeterminant
import Mathlib.LinearAlgebra.Matrix.SchurComplement
import Mathlib.Algebra.BigOperators.Fin

/-!
# Hessian determinant of an interior monomial

For an exponent vector `d`, put

    M(d) = d dᵀ - diag(d).

This is the numerical Hessian core of the monomial `x^d` after evaluation at
`(1,1,1,1)`.  In four variables

    det M(d) = (∏ᵢ dᵢ) (1 - ∑ᵢ dᵢ).

Thus, in characteristic zero, every monomial of ordinary degree at least three
which involves all four variables has nonzero Hessian determinant.  This is
the algebraic obstruction used for interior vertices in the first-nonfacet
Newton argument.
-/

namespace HC4.Polynomial

open MvPolynomial
open scoped BigOperators Matrix

noncomputable section

/-- The exponent Hessian core `d dᵀ - diag(d)`. -/
def exponentHessianCore {K : Type*} [CommRing K]
    (d : Fin 4 →₀ ℕ) : Matrix (Fin 4) (Fin 4) K :=
  fun i j => (d i : K) * (d j : K) - if i = j then (d i : K) else 0

/-- Casted predecessor identity used on diagonal Hessian entries. -/
theorem natCast_mul_pred {K : Type*} [CommRing K] (n : ℕ) :
    (n : K) * ((n - 1 : ℕ) : K) = (n : K) ^ 2 - (n : K) := by
  cases n <;> simp <;> ring

/-- Factorisation of the exponent Hessian core into a diagonal matrix and a
rank-one perturbation of the identity. -/
theorem exponentHessianCore_factor {K : Type*} [CommRing K]
    (d : Fin 4 →₀ ℕ) :
    exponentHessianCore (K := K) d =
      Matrix.diagonal (fun i : Fin 4 => -(d i : K)) *
        (1 +
          Matrix.replicateCol Unit (fun _ : Fin 4 => (1 : K)) *
            Matrix.replicateRow Unit (fun i : Fin 4 => -(d i : K))) := by
  classical
  ext i j
  rw [Matrix.mul_apply]
  rw [Finset.sum_eq_single i]
  · by_cases h : i = j
    · subst j
      simp [exponentHessianCore, Matrix.mul_apply] <;> ring
    · simp [exponentHessianCore, Matrix.mul_apply, h] <;> ring
  · intro k hk hki
    have hik : i ≠ k := Ne.symm hki
    simp [Matrix.diagonal_apply, hik]
  · simp

/-- Determinant formula for the four-variable exponent Hessian core. -/
theorem det_exponentHessianCore {K : Type*} [CommRing K]
    (d : Fin 4 →₀ ℕ) :
    (exponentHessianCore (K := K) d).det =
      (∏ i : Fin 4, (d i : K)) * (1 - ∑ i : Fin 4, (d i : K)) := by
  rw [exponentHessianCore_factor, Matrix.det_mul, Matrix.det_diagonal,
    Matrix.det_one_add_replicateCol_mul_replicateRow]
  have hneg : (∏ i : Fin 4, -(d i : K)) = ∏ i : Fin 4, (d i : K) := by
    simp [Fin.prod_univ_four] <;> ring
  rw [hneg]
  simp [dotProduct, Fin.sum_univ_four] <;> ring

/-- Evaluating the Hessian of a monomial at `(1,1,1,1)` gives its coefficient
 times the exponent Hessian core. -/
theorem eval_one_hessian_monomial {K : Type*} [CommRing K]
    (d : Fin 4 →₀ ℕ) (c : K) :
    (MvPolynomial.eval fun _ : Fin 4 => (1 : K)).mapMatrix
        (hessian (MvPolynomial.monomial d c)) =
      c • exponentHessianCore (K := K) d := by
  classical
  ext i j
  by_cases hij : i = j
  · subst j
    cases hdi : d i with
    | zero =>
        simp [hessian_apply, exponentHessianCore, MvPolynomial.pderiv_monomial,
          MvPolynomial.eval_monomial, hdi]
    | succ n =>
        simp [hessian_apply, exponentHessianCore, MvPolynomial.pderiv_monomial,
          MvPolynomial.eval_monomial, Finsupp.prod, hdi] <;> ring
  · simp [hessian_apply, exponentHessianCore, MvPolynomial.pderiv_monomial,
      MvPolynomial.eval_monomial, Finsupp.prod, hij] <;> ring

/-- Evaluation of the monomial Hessian determinant at one. -/
theorem eval_one_hessianDeterminant_monomial {K : Type*} [CommRing K]
    (d : Fin 4 →₀ ℕ) (c : K) :
    MvPolynomial.eval (fun _ : Fin 4 => (1 : K))
        (hessianDeterminant (MvPolynomial.monomial d c)) =
      c ^ 4 * (exponentHessianCore (K := K) d).det := by
  unfold hessianDeterminant
  rw [RingHom.map_det]
  rw [eval_one_hessian_monomial]
  simpa using Matrix.det_smul (exponentHessianCore (K := K) d) c

/-- An exponent involving every variable and of degree at least three has
nonzero exponent-Hessian determinant over a characteristic-zero field. -/
theorem det_exponentHessianCore_ne_zero
    {K : Type*} [Field K] [CharZero K]
    {d : Fin 4 →₀ ℕ}
    (hpos : ∀ i : Fin 4, 0 < d i)
    (hdeg : 3 ≤ ordinaryDegree4 d) :
    (exponentHessianCore (K := K) d).det ≠ 0 := by
  rw [det_exponentHessianCore]
  apply mul_ne_zero
  · apply Finset.prod_ne_zero_iff.mpr
    intro i hi
    exact_mod_cast (Nat.ne_of_gt (hpos i))
  · have hsum : (∑ i : Fin 4, (d i : K)) = (ordinaryDegree4 d : K) := by
      simp [ordinaryDegree4, Fin.sum_univ_four]
    rw [hsum]
    intro hzero
    have hone : (ordinaryDegree4 d : K) = 1 := (sub_eq_zero.mp hzero).symm
    have honeNat : ordinaryDegree4 d = 1 := by exact_mod_cast hone
    omega

/-- **Interior monomial obstruction.**  A nonzero monomial of degree at least
three which involves all four variables cannot have identically zero Hessian
determinant in characteristic zero. -/
theorem hessianDeterminant_monomial_ne_zero
    {K : Type*} [Field K] [CharZero K]
    {d : Fin 4 →₀ ℕ} {c : K}
    (hc : c ≠ 0)
    (hpos : ∀ i : Fin 4, 0 < d i)
    (hdeg : 3 ≤ ordinaryDegree4 d) :
    hessianDeterminant (MvPolynomial.monomial d c) ≠ 0 := by
  intro hzero
  have heval := congrArg
    (MvPolynomial.eval fun _ : Fin 4 => (1 : K)) hzero
  rw [eval_one_hessianDeterminant_monomial] at heval
  simp only [map_zero] at heval
  have hcore := det_exponentHessianCore_ne_zero (K := K) hpos hdeg
  exact (mul_ne_zero (pow_ne_zero 4 hc) hcore) heval

end

end HC4.Polynomial
