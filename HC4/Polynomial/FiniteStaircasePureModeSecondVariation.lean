import HC4.Polynomial.FiniteStaircasePureModeMixedDeterminant
import Mathlib.Algebra.DualNumber
import Mathlib.Tactic

/-!
# Second variation of the two pure finite-staircase modes

The one-fibre extreme diagonals reduce, after the common affine translation,
to literal pure longitudinal modes.  The second-order parameter-gap jet uses
nested dual numbers and sends a linear matrix pencil `A + t B` to

    ((A,B),(B,0)).

Its doubly-nilpotent determinant component is twice the quadratic coefficient
of `det(A+tB)`.  For the two endpoint/pure-mode exponent cores that component
has an explicit nonzero factorisation.

This file is state-free.  The source-facing adapter only has to identify the
endpoint and interior moment matrices after evaluation at the common affine
root.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

universe u
variable {K : Type u} [CommRing K]

/-- Nested-dual second jet of the highest endpoint and upper pure interior
exponent cores, with arbitrary scalar multipliers. -/
def highestUpperPureModeSecondJet
    (V n k a b : K) :
    Matrix (Fin 4) (Fin 4) (DualNumber (DualNumber K)) :=
  let A := fieldExponentHessianCore ![1, n - 1, 0, V * (n - 1)]
  let B := fieldExponentHessianCore ![k, 0, 1, V * k]
  fun i j => ((a * A i j, b * B i j), (b * B i j, 0))

set_option maxHeartbeats 2000000

/-- **Highest/upper pure second variation.** -/
theorem snd_snd_det_highestUpperPureModeSecondJet
    (V n k a b : K) :
    TrivSqZeroExt.snd
      (TrivSqZeroExt.snd
        (highestUpperPureModeSecondJet V n k a b).det) =
      2 * V * (V + 1) * (n - 1) ^ 2 * k ^ 2 * (n - 2) *
        a ^ 2 * b ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [highestUpperPureModeSecondJet, fieldExponentHessianCore,
    Matrix.det_fin_three, Fin.succAbove]
  ring

/-- Nested-dual second jet of the locked endpoint and lower pure interior
exponent cores, with arbitrary scalar multipliers. -/
def lockedLowerPureModeSecondJet
    (V ell k a b : K) :
    Matrix (Fin 4) (Fin 4) (DualNumber (DualNumber K)) :=
  let A := fieldExponentHessianCore ![1, 0, ell, ell * V]
  let B := fieldExponentHessianCore ![k - 1, 1, 0, V * (k - 1)]
  fun i j => ((a * A i j, b * B i j), (b * B i j, 0))

/-- **Locked/lower pure second variation.** -/
theorem snd_snd_det_lockedLowerPureModeSecondJet
    (V ell k a b : K) :
    TrivSqZeroExt.snd
      (TrivSqZeroExt.snd
        (lockedLowerPureModeSecondJet V ell k a b).det) =
      2 * V * (V + 1) * ell ^ 2 * (ell - 1) * (k - 1) ^ 2 *
        a ^ 2 * b ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [lockedLowerPureModeSecondJet, fieldExponentHessianCore,
    Matrix.det_fin_three, Fin.succAbove]
  ring

end

end HC4.Polynomial
