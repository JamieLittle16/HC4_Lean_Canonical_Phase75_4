import HC4.Newton.GeneralFourBlockSchur
import Mathlib.Tactic

/-!
# Cleared 1+3 Schur quotient of a symmetric four-block

For a symmetric four-block

    [ a  b  p  q ]
    [ b  d  r  s ]
    [ p  r  x  y ]
    [ q  s  y  z ]

with a distinguished first coordinate, the denominator-cleared Schur
complement of the scalar pivot a is the symmetric 3x3 matrix

    [ ad-b^2   ar-bp   as-bq ]
    [ ar-bp    ax-p^2  ay-pq ]
    [ as-bq    ay-pq   az-q^2 ].

Its determinant is exactly

    a^2 * det(H).

This is the natural quotient clock for a rank-one special fibre.  Unlike the
existing 2+2 Schur block, it only needs one nonzero scalar pivot and is
therefore applicable when the constant Hessian itself has rank exactly one.

The theorem is a fixed finite polynomial identity over an arbitrary
commutative ring.
-/

namespace HC4.Newton

open scoped Matrix

noncomputable section

variable {R : Type*} [CommRing R]

namespace GeneralFourBlock

/-- Denominator-cleared 3x3 Schur quotient after pivoting on coordinate 0. -/
def rankOneClearedThreeSchurMatrix
    (H : GeneralFourBlock R) : Matrix (Fin 3) (Fin 3) R :=
  !![
    H.a * H.d - H.b * H.b,
      H.a * H.r - H.b * H.p,
      H.a * H.s - H.b * H.q;
    H.a * H.r - H.b * H.p,
      H.a * H.x - H.p * H.p,
      H.a * H.y - H.p * H.q;
    H.a * H.s - H.b * H.q,
      H.a * H.y - H.p * H.q,
      H.a * H.z - H.q * H.q
  ]

/-- Exact determinant identity for the cleared rank-one quotient. -/
theorem det_rankOneClearedThreeSchurMatrix
    (H : GeneralFourBlock R) :
    (H.rankOneClearedThreeSchurMatrix).det =
      H.a ^ 2 * H.determinantCore := by
  simp [rankOneClearedThreeSchurMatrix, Matrix.det_fin_three,
    determinantCore]
  ring

/-- The determinant identity in matrix form. -/
theorem det_rankOneClearedThreeSchurMatrix_eq_matrix_det
    (H : GeneralFourBlock R) :
    (H.rankOneClearedThreeSchurMatrix).det =
      H.a ^ 2 * H.matrix.det := by
  rw [H.det_rankOneClearedThreeSchurMatrix, H.matrix_det]

/-- If the full determinant is an exact pure parameter clock, the cleared
rank-one quotient retains the same closing exponent and acquires only the
square of the scalar pivot as clearing factor. -/
theorem det_rankOneClearedThreeSchurMatrix_of_fullDet_X_pow
    {S : Type*} [CommRing S]
    (H : GeneralFourBlock (Polynomial S))
    (Delta : Nat)
    (hdet : H.determinantCore = Polynomial.X ^ Delta) :
    (H.rankOneClearedThreeSchurMatrix).det =
      H.a ^ 2 * Polynomial.X ^ Delta := by
  rw [H.det_rankOneClearedThreeSchurMatrix, hdet]

/-- Entrywise zero criterion for the cleared quotient.  This is the exact
rank-one scalar-pivot relation at the special fibre. -/
theorem rankOneClearedThreeSchurMatrix_eq_zero
    (H : GeneralFourBlock R)
    (had : H.a * H.d = H.b * H.b)
    (har : H.a * H.r = H.b * H.p)
    (has : H.a * H.s = H.b * H.q)
    (hax : H.a * H.x = H.p * H.p)
    (hay : H.a * H.y = H.p * H.q)
    (haz : H.a * H.z = H.q * H.q) :
    H.rankOneClearedThreeSchurMatrix = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [rankOneClearedThreeSchurMatrix, had, har, has, hax, hay, haz]

end GeneralFourBlock

end

end HC4.Newton
