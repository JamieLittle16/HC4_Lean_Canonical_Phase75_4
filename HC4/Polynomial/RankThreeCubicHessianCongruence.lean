import HC4.Polynomial.RankThreeCubicTensorRankOnePlane
import Mathlib.Tactic

/-!
# The coordinate-invariant matrix core of cubic rank-one plane closure

A linear substitution of a cubic Hessian sends its coefficient
matrix H to Mᵀ H M. The following results are over any field:

* Vanishing of every 2x2 cofactor (adjugate = 0) is preserved by
  congruence, even when M is singular.
* The nonzero determinant of H is preserved if M has nonzero
  determinant.

These are the precise algebraic transformations needed when the
arbitrary linear pole p is moved to a coordinate hyperplane.
They do not assume that the pole has already been straightened.
-/

namespace HC4.Polynomial.RankThreeCubic

open scoped Matrix BigOperators

noncomputable section

/-- If every cofactor of a 3x3 matrix vanishes, then every
cofactor of its congruence transform vanishes. No invertibility
assumption on the change-of-coordinates matrix is necessary. -/
theorem adjugate_zero_of_matrix_congruence
    {R : Type*} [CommRing R]
    (H M : Matrix (Fin 3) (Fin 3) R)
    (hzero : H.adjugate = 0) :
    (M.transpose * H * M).adjugate = 0 := by
  rw [Matrix.adjugate_mul_distrib,
    Matrix.adjugate_mul_distrib, hzero]
  simp

/-- A nonzero determinant remains nonzero after an invertible
congruence. This is the Hessian nondegeneracy part of adapting
the source coordinate chart to an arbitrary linear pole. -/
theorem det_ne_zero_of_matrix_congruence
    {K : Type*} [Field K]
    (H M : Matrix (Fin 3) (Fin 3) K)
    (hH : H.det ≠ 0)
    (hM : M.det ≠ 0) :
    (M.transpose * H * M).det ≠ 0 := by
  simpa only [Matrix.det_mul, Matrix.det_transpose] using
    (mul_ne_zero (mul_ne_zero hM hH) hM)

/-- One direction of the rank-one-plane obstruction is invariant:
if a congruence has a nonzero cofactor, the original matrix must
also have a nonzero cofactor. Unlike matrix rank, this is a
pure polynomial-ring argument. -/
theorem adjugate_ne_zero_of_congruence
    {R : Type*} [CommRing R]
    (H M : Matrix (Fin 3) (Fin 3) R)
    (h : (M.transpose * H * M).adjugate ≠ 0) :
    H.adjugate ≠ 0 := by
  intro hz
  exact h (adjugate_zero_of_matrix_congruence H M hz)

end
end HC4.Polynomial.RankThreeCubic
