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


/-- Denominator-cleared 3x3 Schur quotient after pivoting on coordinate 1. -/
def rankOneClearedThreeSchurMatrixD
    (H : GeneralFourBlock R) : Matrix (Fin 3) (Fin 3) R :=
  !![
    H.d * H.a - H.b * H.b,
      H.d * H.p - H.b * H.r,
      H.d * H.q - H.b * H.s;
    H.d * H.p - H.b * H.r,
      H.d * H.x - H.r * H.r,
      H.d * H.y - H.r * H.s;
    H.d * H.q - H.b * H.s,
      H.d * H.y - H.r * H.s,
      H.d * H.z - H.s * H.s
  ]

/-- Exact determinant identity for the coordinate-1 scalar pivot. -/
theorem det_rankOneClearedThreeSchurMatrixD
    (H : GeneralFourBlock R) :
    (H.rankOneClearedThreeSchurMatrixD).det =
      H.d ^ 2 * H.determinantCore := by
  simp [rankOneClearedThreeSchurMatrixD, Matrix.det_fin_three,
    determinantCore]
  ring

/-- Denominator-cleared 3x3 Schur quotient after pivoting on coordinate 2. -/
def rankOneClearedThreeSchurMatrixX
    (H : GeneralFourBlock R) : Matrix (Fin 3) (Fin 3) R :=
  !![
    H.x * H.a - H.p * H.p,
      H.x * H.b - H.p * H.r,
      H.x * H.q - H.p * H.y;
    H.x * H.b - H.p * H.r,
      H.x * H.d - H.r * H.r,
      H.x * H.s - H.r * H.y;
    H.x * H.q - H.p * H.y,
      H.x * H.s - H.r * H.y,
      H.x * H.z - H.y * H.y
  ]

/-- Exact determinant identity for the coordinate-2 scalar pivot. -/
theorem det_rankOneClearedThreeSchurMatrixX
    (H : GeneralFourBlock R) :
    (H.rankOneClearedThreeSchurMatrixX).det =
      H.x ^ 2 * H.determinantCore := by
  simp [rankOneClearedThreeSchurMatrixX, Matrix.det_fin_three,
    determinantCore]
  ring

/-- Pure-clock form for the coordinate-1 scalar pivot. -/
theorem det_rankOneClearedThreeSchurMatrixD_of_fullDet_X_pow
    {S : Type*} [CommRing S]
    (H : GeneralFourBlock (Polynomial S))
    (Delta : Nat)
    (hdet : H.determinantCore = Polynomial.X ^ Delta) :
    (H.rankOneClearedThreeSchurMatrixD).det =
      H.d ^ 2 * Polynomial.X ^ Delta := by
  rw [H.det_rankOneClearedThreeSchurMatrixD, hdet]

/-- Pure-clock form for the coordinate-2 scalar pivot. -/
theorem det_rankOneClearedThreeSchurMatrixX_of_fullDet_X_pow
    {S : Type*} [CommRing S]
    (H : GeneralFourBlock (Polynomial S))
    (Delta : Nat)
    (hdet : H.determinantCore = Polynomial.X ^ Delta) :
    (H.rankOneClearedThreeSchurMatrixX).det =
      H.x ^ 2 * Polynomial.X ^ Delta := by
  rw [H.det_rankOneClearedThreeSchurMatrixX, hdet]

end GeneralFourBlock

end

end HC4.Newton
