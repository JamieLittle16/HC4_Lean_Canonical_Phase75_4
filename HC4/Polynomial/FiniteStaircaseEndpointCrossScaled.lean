import HC4.Polynomial.FiniteStaircaseEndpointCrossVariation
import HC4.Polynomial.FiniteStaircaseThreeLayerIntermediateVariation
import Mathlib.Tactic

/-!
# Scaled endpoint cross variation

The actual evaluated endpoint moment matrices carry nonzero scalar factors.
This records the cross first variation with those scalars left explicit.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

universe u
variable {K : Type u} [CommRing K]

/-- **Scaled locked-to-highest endpoint first variation.** -/
theorem snd_det_endpointDualPencil_scaled_lockedHighest
    (V ell n lamLo lamHi : K) :
    TrivSqZeroExt.snd
      (endpointDualPencil
        (lamLo • lockedDoubleRootMomentCore V ell)
        (lamHi • highestDoubleRootMomentCore V n)).det =
      lamLo ^ 3 * lamHi *
        (4 * V * (V + 1) * ell ^ 3 * n *
          (ell + 1) ^ 3 * (n - 1) ^ 2) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [endpointDualPencil,
    lockedDoubleRootMomentCore, highestDoubleRootMomentCore,
    staircaseLogDirection, lineMomentHessian,
    rankThreeLogBaseExponent, rankThreeLogDirection,
    Matrix.det_fin_three, Fin.succAbove]
  ring

end

end HC4.Polynomial
