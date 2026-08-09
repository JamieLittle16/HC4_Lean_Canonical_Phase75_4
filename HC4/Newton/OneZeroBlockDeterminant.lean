import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Determinant of the one-zero Hessian block

The one-zero Hessian has the generic sparse shape

    [ a  p  b  c ]
    [ q  0  0  0 ]
    [ r  0  e  f ]
    [ s  0  g  h ].

Its determinant is

    -p*q*(e*h - f*g).

For an actual Hessian, symmetry gives `p=q`, yielding the square factor

    -p^2 * (e*h - f*g).

This is the algebraic core of the one-zero endpoint.
-/

namespace HC4.Newton

open scoped Matrix

noncomputable section

/-- Generic matrix carrying the one-zero sparse Hessian shape. -/
def oneZeroHessianBlockMatrix
    {R : Type*} [CommRing R]
    (a p b c q r e f s g h : R) :
    Matrix (Fin 4) (Fin 4) R :=
  !![a, p, b, c;
     q, 0, 0, 0;
     r, 0, e, f;
     s, 0, g, h]

/-- Exact determinant formula for the one-zero sparse block. -/
theorem det_oneZeroHessianBlockMatrix
    {R : Type*} [CommRing R]
    (a p b c q r e f s g h : R) :
    (oneZeroHessianBlockMatrix
      a p b c q r e f s g h).det =
      -(p * q) * (e * h - f * g) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [oneZeroHessianBlockMatrix,
    Matrix.det_fin_three, Fin.succAbove]
  ring

end

end HC4.Newton
