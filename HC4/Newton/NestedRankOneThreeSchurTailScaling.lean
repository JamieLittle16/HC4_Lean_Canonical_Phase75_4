import HC4.Newton.RankOneThreeToBinarySchur
import Mathlib.Tactic

/-!
# Common-factor scaling for the second scalar Schur step

The normalised 3x3 tail in the HC4 top-kernel seam is obtained by removing
one common scalar factor from every entry of a symmetric 3x3 polynomial
matrix.  Since each denominator-cleared 1+2 Schur entry is quadratic in the
3x3 entries, the second-stage binary Schur series acquires exactly the square
of that common factor.

This file records the statement over an arbitrary commutative ring and for
both active pivots used by the HC4 positive-tail construction.
-/

namespace HC4.Newton

noncomputable section

variable {R : Type*} [CommRing R]

/-- Entrywise multiplication of a 3x3 matrix by one common scalar. -/
def commonScaleThreeMatrix
    (c : R)
    (M : Matrix (Fin 3) (Fin 3) R) :
    Matrix (Fin 3) (Fin 3) R :=
  fun i j => c * M i j

@[simp] theorem threePivot0BinarySchurSeries_commonScale_active
    (c : Polynomial R) (M : Matrix (Fin 3) (Fin 3) (Polynomial R)) :
    (threePivot0BinarySchurSeries (commonScaleThreeMatrix c M)).active =
      c ^ 2 * (threePivot0BinarySchurSeries M).active := by
  simp [threePivot0BinarySchurSeries, commonScaleThreeMatrix]
  ring

@[simp] theorem threePivot0BinarySchurSeries_commonScale_offDiag
    (c : Polynomial R) (M : Matrix (Fin 3) (Fin 3) (Polynomial R)) :
    (threePivot0BinarySchurSeries (commonScaleThreeMatrix c M)).offDiag =
      c ^ 2 * (threePivot0BinarySchurSeries M).offDiag := by
  simp [threePivot0BinarySchurSeries, commonScaleThreeMatrix]
  ring

@[simp] theorem threePivot0BinarySchurSeries_commonScale_kernel
    (c : Polynomial R) (M : Matrix (Fin 3) (Fin 3) (Polynomial R)) :
    (threePivot0BinarySchurSeries (commonScaleThreeMatrix c M)).kernel =
      c ^ 2 * (threePivot0BinarySchurSeries M).kernel := by
  simp [threePivot0BinarySchurSeries, commonScaleThreeMatrix]
  ring

@[simp] theorem threePivot1BinarySchurSeries_commonScale_active
    (c : Polynomial R) (M : Matrix (Fin 3) (Fin 3) (Polynomial R)) :
    (threePivot1BinarySchurSeries (commonScaleThreeMatrix c M)).active =
      c ^ 2 * (threePivot1BinarySchurSeries M).active := by
  simp [threePivot1BinarySchurSeries, commonScaleThreeMatrix]
  ring

@[simp] theorem threePivot1BinarySchurSeries_commonScale_offDiag
    (c : Polynomial R) (M : Matrix (Fin 3) (Fin 3) (Polynomial R)) :
    (threePivot1BinarySchurSeries (commonScaleThreeMatrix c M)).offDiag =
      c ^ 2 * (threePivot1BinarySchurSeries M).offDiag := by
  simp [threePivot1BinarySchurSeries, commonScaleThreeMatrix]
  ring

@[simp] theorem threePivot1BinarySchurSeries_commonScale_kernel
    (c : Polynomial R) (M : Matrix (Fin 3) (Fin 3) (Polynomial R)) :
    (threePivot1BinarySchurSeries (commonScaleThreeMatrix c M)).kernel =
      c ^ 2 * (threePivot1BinarySchurSeries M).kernel := by
  simp [threePivot1BinarySchurSeries, commonScaleThreeMatrix]
  ring

end

end HC4.Newton
