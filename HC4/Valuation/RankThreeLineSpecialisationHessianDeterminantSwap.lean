import HC4.Valuation.RankThreeLineSpecialisationHessianParameterSwap
import HC4.Polynomial.ComplementaryMvMomentRealisation
import Mathlib.Algebra.Polynomial.Bivariate
import Mathlib.Tactic

/-!
# Determinant bridge for the swapped specialised Euler Hessian

The ordinary source Hessian determinant lives over the polynomial parameter
ring.  For the finite-staircase coefficient argument we instead use the
Euler-scaled Hessian, line-specialise it, and swap the family and longitudinal
variables.  All three operations preserve determinant zero.

The existing Euler-scaled determinant identity was stated over a field.  Its
proof is purely commutative-ring algebra, so we record the coefficient-ring
version needed for a source family over `K[τ]`.
-/

namespace HC4.Polynomial

open scoped Matrix BigOperators

noncomputable section

/-- Ring-theoretic form of the Euler-scaled determinant identity. -/
theorem det_eulerScaledHessian_eq_coordinate_square_mul_hessianDeterminant_commRing
    {R : Type*} [CommRing R]
    (p : MvPolynomial (Fin 4) R) :
    (eulerScaledHessian p).det =
      (∏ i : Fin 4, MvPolynomial.X i)^2 * hessianDeterminant p := by
  let D : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 4) R) :=
    Matrix.diagonal (fun i => MvPolynomial.X i)
  let H : Matrix (Fin 4) (Fin 4) (MvPolynomial (Fin 4) R) :=
    Matrix.transpose (hessian p)
  have hmatrix : eulerScaledHessian p = D * H * D := by
    apply Matrix.ext
    intro i j
    simp [D, H, eulerScaledHessian_apply, hessian_apply]
    ring
  rw [hmatrix, Matrix.det_mul, Matrix.det_mul]
  simp [D, H, hessianDeterminant]
  ring

end

end HC4.Polynomial

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial
open scoped Matrix Polynomial.Bivariate

universe u
variable {K : Type u} [Field K]

/-- **Swapped specialised determinant remains zero.**  If a polynomial-
parameter source family has identically zero Hessian determinant, then its
swapped rank-three specialised Euler-Hessian matrix has identically zero
determinant in `K[X][τ]`. -/
theorem det_swappedRankThreeEulerHessian_eq_zero_of_hessianDeterminant_eq_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdet : hessianDeterminant P = 0) :
    (swappedRankThreeEulerHessian P).det = 0 := by
  have heuler : (eulerScaledHessian P).det = 0 := by
    rw [det_eulerScaledHessian_eq_coordinate_square_mul_hessianDeterminant_commRing]
    rw [hdet]
    simp
  let sp : MvPolynomial (Fin 4) (Polynomial K) →+*
      Polynomial (Polynomial K) := rankThreeLineSpecialisation
  have hsp : (sp.mapMatrix (eulerScaledHessian P)).det = 0 := by
    rw [← RingHom.map_det sp]
    simpa [sp] using congrArg sp heuler
  let sw : Polynomial (Polynomial K) ≃ₐ[K] Polynomial (Polynomial K) :=
    Polynomial.Bivariate.swap
  have hswap : (sw.mapMatrix (sp.mapMatrix (eulerScaledHessian P))).det = 0 := by
    rw [← AlgEquiv.map_det sw]
    simpa [sw] using congrArg sw hsp
  have hmatrix :
      sw.mapMatrix (sp.mapMatrix (eulerScaledHessian P)) =
        swappedRankThreeEulerHessian P := by
    apply Matrix.ext
    intro i j
    rfl
  rw [hmatrix] at hswap
  exact hswap

end

end HC4.Valuation
