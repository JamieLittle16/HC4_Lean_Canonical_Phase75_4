import HC4.Newton.ZeroSchurFirstEntryClock
import Mathlib.Tactic

/-!
# Cleared 1+2 Schur quotient of a symmetric 3x3 polynomial matrix

This is the second finite Schur step used after the 1+3 quotient of a
rank-one four-dimensional special fibre.

For a symmetric 3x3 matrix

    [ a b c ]
    [ b d e ]
    [ c e f ]

the denominator-cleared binary Schur quotient at pivot a is

    [ ad-b^2   ae-bc ]
    [ ae-bc    af-c^2 ]

and its determinant is

    a * det(M).

The same identity is recorded for pivots d and f.  The resulting binary
series is exactly the `BinarySchurPolynomialSeries` already consumed by the
green zero-Schur first-entry machinery.
-/

namespace HC4.Newton

noncomputable section

variable {R : Type*} [CommRing R]

/-- Cleared binary quotient of a symmetric 3x3 series using coordinate 0 as
scalar pivot. -/
def threePivot0BinarySchurSeries
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R)) :
    BinarySchurPolynomialSeries R where
  active := M 0 0 * M 1 1 - M 0 1 * M 0 1
  offDiag := M 0 0 * M 1 2 - M 0 1 * M 0 2
  kernel := M 0 0 * M 2 2 - M 0 2 * M 0 2

/-- Coordinate-1 pivot, retaining coordinates 0 and 2. -/
def threePivot1BinarySchurSeries
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R)) :
    BinarySchurPolynomialSeries R where
  active := M 1 1 * M 0 0 - M 0 1 * M 0 1
  offDiag := M 1 1 * M 0 2 - M 0 1 * M 1 2
  kernel := M 1 1 * M 2 2 - M 1 2 * M 1 2

/-- Coordinate-2 pivot, retaining coordinates 0 and 1. -/
def threePivot2BinarySchurSeries
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R)) :
    BinarySchurPolynomialSeries R where
  active := M 2 2 * M 0 0 - M 0 2 * M 0 2
  offDiag := M 2 2 * M 0 1 - M 0 2 * M 1 2
  kernel := M 2 2 * M 1 1 - M 1 2 * M 1 2

/-- Exact determinant identity for the coordinate-0 pivot. -/
theorem threePivot0BinarySchurSeries_determinant
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R))
    (hsymm : M.IsSymm) :
    (threePivot0BinarySchurSeries M).determinant =
      M 0 0 * M.det := by
  have h10 : M 1 0 = M 0 1 := hsymm 1 0
  have h20 : M 2 0 = M 0 2 := hsymm 2 0
  have h21 : M 2 1 = M 1 2 := hsymm 2 1
  simp [threePivot0BinarySchurSeries,
    BinarySchurPolynomialSeries.determinant, Matrix.det_fin_three,
    h10, h20, h21]
  ring

/-- Exact determinant identity for the coordinate-1 pivot. -/
theorem threePivot1BinarySchurSeries_determinant
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R))
    (hsymm : M.IsSymm) :
    (threePivot1BinarySchurSeries M).determinant =
      M 1 1 * M.det := by
  have h10 : M 1 0 = M 0 1 := hsymm 1 0
  have h20 : M 2 0 = M 0 2 := hsymm 2 0
  have h21 : M 2 1 = M 1 2 := hsymm 2 1
  simp [threePivot1BinarySchurSeries,
    BinarySchurPolynomialSeries.determinant, Matrix.det_fin_three,
    h10, h20, h21]
  ring

/-- Exact determinant identity for the coordinate-2 pivot. -/
theorem threePivot2BinarySchurSeries_determinant
    (M : Matrix (Fin 3) (Fin 3) (Polynomial R))
    (hsymm : M.IsSymm) :
    (threePivot2BinarySchurSeries M).determinant =
      M 2 2 * M.det := by
  have h10 : M 1 0 = M 0 1 := hsymm 1 0
  have h20 : M 2 0 = M 0 2 := hsymm 2 0
  have h21 : M 2 1 = M 1 2 := hsymm 2 1
  simp [threePivot2BinarySchurSeries,
    BinarySchurPolynomialSeries.determinant, Matrix.det_fin_three,
    h10, h20, h21]
  ring

end

end HC4.Newton
