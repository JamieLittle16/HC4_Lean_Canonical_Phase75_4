import HC4.Valuation.QuadraticTransverseCapSourceAxisRiccati
import Mathlib.Tactic

/-!
# Actual four-variable quadratic-cap Hessian: division-free MATRIX Riccati

This is the source-level endpoint of the twice-differentiated
constant-Hessian-determinant calculation. It combines the nine
source-axis scalar identities into the genuine matrix identity

  det(C) * C'' = 2 * C' * adj(C) * C'

where C(x) is the original source's transverse 3x3 Hessian.
No assumed Riccati equation, invertible transverse block, rational
differential operator, or endpoint data appears in the statement.

The next regular-rank step can localize this identity at det C.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix BigOperators

set_option maxHeartbeats 4000000

variable {K : Type*} [Field K]

/-- The division-free polynomial matrix Riccati equation for the
ORIGINAL four-variable potential, with no generic-rank hypothesis.

This is the concrete matrix identity consumed by reciprocal rigidity,
rather than a family of abstract Schur variables. -/
theorem quadraticTransverseCapSource_matrixRiccati
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    let C := (quadraticTransverseCapSourceAxisThreeBlock F).matrix
    let C' : Matrix (Fin 3) (Fin 3) (Polynomial K) :=
      fun i j => Polynomial.derivative (C i j)
    let C'' : Matrix (Fin 3) (Fin 3) (Polynomial K) :=
      fun i j => Polynomial.derivative (Polynomial.derivative (C i j))
    C.det • C'' = 2 • ((C' * C.adjugate) * C') := by
  classical
  let T := quadraticTransverseCapSourceAxisThreeBlock F
  let C : Matrix (Fin 3) (Fin 3) (Polynomial K) := T.matrix
  let C' : Matrix (Fin 3) (Fin 3) (Polynomial K) :=
    fun i j => Polynomial.derivative (C i j)
  let C'' : Matrix (Fin 3) (Fin 3) (Polynomial K) :=
    fun i j => Polynomial.derivative (Polynomial.derivative (C i j))
  have hdetCore : C.det = T.determinantCore :=
    GeneralThreeBlock.matrix_det T
  have hcontract (i j : Fin 3) :
      ((C' * C.adjugate) * C') i j =
        C' 0 i * quadraticTransverseAdjugateVector0 T
          (C' 0 j) (C' 1 j) (C' 2 j) +
        C' 1 i * quadraticTransverseAdjugateVector1 T
          (C' 0 j) (C' 1 j) (C' 2 j) +
        C' 2 i * quadraticTransverseAdjugateVector2 T
          (C' 0 j) (C' 1 j) (C' 2 j) := by
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Matrix.adjugate_fin_three,
        Fin.sum_univ_three, C', C, GeneralThreeBlock.matrix,
        quadraticTransverseAdjugateVector0,
        quadraticTransverseAdjugateVector1,
        quadraticTransverseAdjugateVector2] <;>
      ring
  apply Matrix.ext
  intro i j
  have hij :=
    quadraticTransverseCapSource_axisRiccatiCoefficient
      F hbound hdet i j
  change
    C'' i j * T.determinantCore =
      2 * (
        C' 0 i * quadraticTransverseAdjugateVector0 T
          (C' 0 j) (C' 1 j) (C' 2 j) +
        C' 1 i * quadraticTransverseAdjugateVector1 T
          (C' 0 j) (C' 1 j) (C' 2 j) +
        C' 2 i * quadraticTransverseAdjugateVector2 T
          (C' 0 j) (C' 1 j) (C' 2 j)) at hij
  change C.det * C'' i j = (2 : Polynomial K) * ((C' * C.adjugate) * C') i j
  rw [hdetCore, hcontract]
  simpa only [mul_comm] using hij

end

end HC4.Valuation
