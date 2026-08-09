import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
import Mathlib.Tactic

/-!
# Determinant of the two-zero Hessian block

The two-zero terminal Hessian has the shape

    [ a  b  p  r ]
    [ c  d  q  s ]
    [ p  q  0  0 ]
    [ r  s  0  0 ].

Its determinant is independent of the upper-left block and equals

    (p*s - q*r)^2.

This is the exact finite determinant identity behind the reduction from
four-dimensional Monge--Ampère to the planar Keller determinant.
-/

namespace HC4.Newton

open scoped Matrix

noncomputable section

/-- Generic matrix carrying the two-zero Hessian block shape. -/
def twoZeroHessianBlockMatrix
    {R : Type*} [CommRing R]
    (a b c d p q r s : R) :
    Matrix (Fin 4) (Fin 4) R :=
  !![a, b, p, r;
     c, d, q, s;
     p, q, 0, 0;
     r, s, 0, 0]

/-- Exact determinant square for the two-zero Hessian block. -/
theorem det_twoZeroHessianBlockMatrix
    {R : Type*} [CommRing R]
    (a b c d p q r s : R) :
    (twoZeroHessianBlockMatrix
      a b c d p q r s).det =
      (p * s - q * r)^2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [twoZeroHessianBlockMatrix,
    Matrix.det_fin_three, Fin.succAbove]
  ring

end

end HC4.Newton
