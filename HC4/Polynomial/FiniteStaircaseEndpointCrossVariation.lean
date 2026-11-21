import HC4.Polynomial.FiniteStaircaseMiddleDoubleRootVariation
import Mathlib.Algebra.DualNumber
import Mathlib.Tactic

/-!
# Cross variation between the two staircase endpoints

At twice a common affine root the locked and primitive-highest endpoint
moment matrices normalize to `lockedDoubleRootMomentCore` and
`highestDoubleRootMomentCore`.  Their direct first variation is nonzero in
the live positive range.  This is the final state-free obstruction used by
the one-fibre middle-diagonal closure.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

universe u
variable {K : Type u} [CommRing K]

/-- Locked endpoint as constant term, primitive-highest endpoint as the first
variation. -/
def lockedHighestDoubleRootDualPencil
    (V ell n : K) : Matrix (Fin 4) (Fin 4) (DualNumber K) :=
  fun i j =>
    (lockedDoubleRootMomentCore V ell i j,
      highestDoubleRootMomentCore V n i j)

set_option maxHeartbeats 2000000

/-- **Endpoint cross first variation.** -/
theorem snd_det_lockedHighestDoubleRootDualPencil
    (V ell n : K) :
    TrivSqZeroExt.snd (lockedHighestDoubleRootDualPencil V ell n).det =
      4 * V * (V + 1) * ell ^ 3 * n * (ell + 1) ^ 3 * (n - 1) ^ 2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [lockedHighestDoubleRootDualPencil,
    lockedDoubleRootMomentCore, highestDoubleRootMomentCore,
    staircaseLogDirection, lineMomentHessian,
    rankThreeLogBaseExponent, rankThreeLogDirection,
    Matrix.det_fin_three, Fin.succAbove]
  ring

end

end HC4.Polynomial
