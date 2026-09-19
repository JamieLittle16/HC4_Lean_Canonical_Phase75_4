import HC4.Polynomial.FiniteStaircaseEndpointCrossVariation
import Mathlib.Algebra.DualNumber
import Mathlib.Tactic

/-!
# Scaled endpoint cross variation

The actual endpoint matrices obtained after evaluating at twice the common
root carry nonzero scalar factors.  This file records the corresponding
scaled first-variation determinant directly.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

universe u
variable {K : Type u} [CommRing K]

/-- Locked/highest endpoint dual pencil with arbitrary nonzero-normalisation
scalars retained. -/
def scaledLockedHighestDoubleRootDualPencil
    (V ell n lamLo lamHi : K) :
    Matrix (Fin 4) (Fin 4) (DualNumber K) :=
  fun i j =>
    (lamLo * lockedDoubleRootMomentCore V ell i j,
      lamHi * highestDoubleRootMomentCore V n i j)

set_option maxHeartbeats 2000000

/-- **Scaled endpoint cross first variation.** -/
theorem snd_det_scaledLockedHighestDoubleRootDualPencil
    (V ell n lamLo lamHi : K) :
    TrivSqZeroExt.snd
      (scaledLockedHighestDoubleRootDualPencil
        V ell n lamLo lamHi).det =
      4 * V * (V + 1) * ell ^ 3 * n * (ell + 1) ^ 3 *
        (n - 1) ^ 2 * lamLo ^ 3 * lamHi := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [scaledLockedHighestDoubleRootDualPencil,
    lockedDoubleRootMomentCore, highestDoubleRootMomentCore,
    staircaseLogDirection, lineMomentHessian,
    rankThreeLogBaseExponent, rankThreeLogDirection,
    Matrix.det_fin_three, Fin.succAbove]
  ring

end

end HC4.Polynomial
