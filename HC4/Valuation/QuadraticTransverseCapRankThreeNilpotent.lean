import HC4.Valuation.QuadraticTransverseCapRankThreeReciprocalODE
import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
import Mathlib.Tactic

/-!
# Cubic nilpotence of a 3x3 unimodular affine reciprocal

For a 3x3 matrix N over the ground field K, the condition
    det(I + X N) = 1
in K[X] forces N^3=0. This is the precise unipotent/nilpotent
step in the generic-rank-three quadratic transverse cap argument.

This module proves a fully explicit finite-dimensional polynomial
identity and a Cayley–Hamilton identity over arbitrary commutative
rings. In particular it introduces NO abstract nilpotence assumption
when consuming the determinant-one affine-matrix condition.
-/

namespace HC4.Valuation

noncomputable section

variable {K : Type*} [CommRing K]

/-- The first elementary symmetric coefficient of a general
not-necessarily-symmetric 3x3 matrix. -/
def quadraticTransverse_cubicTrace
    (N : Matrix (Fin 3) (Fin 3) K) : K :=
  N 0 0 + N 1 1 + N 2 2

/-- The second elementary symmetric coefficient of the characteristic
polynomial of an arbitrary 3x3 matrix. -/
def quadraticTransverse_cubicSecond
    (N : Matrix (Fin 3) (Fin 3) K) : K :=
  (N 0 0 * N 1 1 + N 0 0 * N 2 2 + N 1 1 * N 2 2) -
    (N 0 1 * N 1 0 + N 0 2 * N 2 0 + N 1 2 * N 2 1)

/-- Exact degree-three determinant expansion for the affine
matrix I+X N, valid over any commutative coefficient ring. -/
theorem quadraticTransverse_det_one_add_X_matrix
    (N : Matrix (Fin 3) (Fin 3) K) :
    (1 + (Polynomial.X : Polynomial K) •
        N.map Polynomial.C).det =
      (1 : Polynomial K) +
      Polynomial.C (quadraticTransverse_cubicTrace N) *
        Polynomial.X +
      Polynomial.C (quadraticTransverse_cubicSecond N) *
        Polynomial.X ^ 2 +
      Polynomial.C N.det * Polynomial.X ^ 3 := by
  simp [Matrix.det_fin_three, Matrix.add_apply, Matrix.smul_apply,
    Matrix.map_apply, Matrix.one_apply,
    quadraticTransverse_cubicTrace, quadraticTransverse_cubicSecond]
  ring

/-- Fully explicit degree-three Cayley–Hamilton identity for a
general 3x3 matrix, without any eigenvalue or diagonalisation argument. -/
theorem quadraticTransverse_cubicMatrix_CH
    (N : Matrix (Fin 3) (Fin 3) K) :
    N ^ 3 -
      (quadraticTransverse_cubicTrace N) • N ^ 2 +
      (quadraticTransverse_cubicSecond N) • N -
      (N.det) • (1 : Matrix (Fin 3) (Fin 3) K) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.det_fin_three,
      Matrix.smul_apply, Matrix.add_apply, Matrix.sub_apply,
      Matrix.one_apply, quadraticTransverse_cubicTrace,
      quadraticTransverse_cubicSecond, pow_succ] <;>
    ring

/-- **Rank-three nilpotent normal form.**

No nilpotence hypothesis is required: it follows from the honest
polynomial determinant condition det(I+X N)=1 using the three
nonconstant coefficients of that determinant and cubic CH. -/
theorem quadraticTransverse_cubicNilpotent_of_affineDet_one
    (N : Matrix (Fin 3) (Fin 3) K)
    (hdet :
      (1 + (Polynomial.X : Polynomial K) •
        N.map Polynomial.C).det = 1) :
    N ^ 3 = 0 := by
  have hp := quadraticTransverse_det_one_add_X_matrix N
  rw [hdet] at hp
  have htrace : quadraticTransverse_cubicTrace N = 0 := by
    have h := congrArg (fun p : Polynomial K => p.coeff 1) hp.symm
    simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow] using h
  have hsecond : quadraticTransverse_cubicSecond N = 0 := by
    have h := congrArg (fun p : Polynomial K => p.coeff 2) hp.symm
    simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow] using h
  have hdetzero : N.det = 0 := by
    have h := congrArg (fun p : Polynomial K => p.coeff 3) hp.symm
    simpa [Polynomial.coeff_add, Polynomial.coeff_C_mul,
      Polynomial.coeff_X_pow] using h
  have hCH := quadraticTransverse_cubicMatrix_CH N
  rw [htrace, hsecond, hdetzero] at hCH
  simpa using hCH

end

end HC4.Valuation
