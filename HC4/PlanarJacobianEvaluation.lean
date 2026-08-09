import HC4.PlanarJC2Interface
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Evaluated planar Jacobian matrix

`PlanarJC2Interface` stores the planar Jacobian determinant as a polynomial.
For the doubling endpoint we also need the evaluated `2 × 2` Jacobian
matrix whose rows are the component polynomials and whose columns are the
source variables.

This file connects the two representations exactly.
-/

namespace HC4

noncomputable section

variable {K : Type*} [Field K]

/-- Evaluated Jacobian matrix of a two-component planar polynomial map.

Rows index output components and columns index source variables. -/
def planarJacobianMatrixAt
    (G : PlanarPolynomialMap K)
    (u : Point2 K) :
    Matrix (Fin 2) (Fin 2) K :=
  fun r c =>
    MvPolynomial.eval u
      (MvPolynomial.pderiv c (G r))

/-- The determinant of the evaluated Jacobian matrix is the evaluation of
the symbolic planar Jacobian determinant. -/
theorem det_planarJacobianMatrixAt
    (G : PlanarPolynomialMap K)
    (u : Point2 K) :
    Matrix.det (planarJacobianMatrixAt G u) =
      MvPolynomial.eval u
        (planarJacobianDetPolynomial G) := by
  simp [planarJacobianMatrixAt,
    planarJacobianDetPolynomial,
    Matrix.det_fin_two]

/-- A planar Keller certificate makes every evaluated Jacobian matrix
nonsingular. -/
theorem planarJacobianMatrixAt_det_ne_zero
    (G : PlanarPolynomialMap K)
    (hKeller :
      HasNonzeroConstantPlanarJacobian G)
    (u : Point2 K) :
    Matrix.det (planarJacobianMatrixAt G u) ≠ 0 := by
  rw [det_planarJacobianMatrixAt]
  exact planarJacobian_crossDet_eval_ne_zero
    G hKeller u

end

end HC4
