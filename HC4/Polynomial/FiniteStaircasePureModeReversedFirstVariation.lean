import HC4.Polynomial.LogHessianMoments
import HC4.Polynomial.RankThreeLogHessian
import Mathlib.Algebra.DualNumber
import Mathlib.Tactic

/-!
# Reversed first variation of the two pure one-fibre modes

The cubic coefficient of a `4 x 4` pencil is the linear coefficient of the
reflected pencil.  For the final A19 pure-mode obstruction we evaluate the
longitudinal variable at twice the common affine root.

After removing the nonzero scalar `u * alpha^m`, a translated pure power of
multiplicity `m` has logarithmic moments

    S0 = 1,
    S1 = 2m,
    S2 = 2m(2m-1).

The endpoint affine profiles have similarly normalized moments.  The two
remaining first-variation determinants are therefore constant ring identities,
recorded here without any HC4 state or source data.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

universe u
variable {K : Type u} [CommRing K]

/-- Common logarithmic direction of the left `(1,V)` staircase. -/
def staircaseLogDirection (V : K) : Fin 4 → K :=
  rankThreeLogDirection 1 (-1) (-1) (-V)

/-- Normalized value at `X=2 alpha` of an upper pure interior mode `j=k`. -/
def upperPureDoubleRootMomentCore
    (V k : K) : Matrix (Fin 4) (Fin 4) K :=
  lineMomentHessian
    (rankThreeLogBaseExponent k (k + 1) (2 * V * k))
    (staircaseLogDirection V)
    1 (2 * k) (2 * k * (2 * k - 1))

/-- Normalized locked endpoint at `X=2 alpha`, after multiplying its affine
profile by `ell+1`. -/
def lockedDoubleRootMomentCore
    (V ell : K) : Matrix (Fin 4) (Fin 4) K :=
  lineMomentHessian
    (rankThreeLogBaseExponent 1 (ell + 1) (V * (ell + 1)))
    (staircaseLogDirection V)
    (ell + 2) (2 * (ell + 1)) (2 * (ell + 1))

/-- Dual-number pencil with the upper pure interior mode as constant part and
the locked endpoint as first variation. -/
def upperPureLockedReverseDualPencil
    (V ell k : K) : Matrix (Fin 4) (Fin 4) (DualNumber K) :=
  fun i j =>
    (upperPureDoubleRootMomentCore V k i j,
      lockedDoubleRootMomentCore V ell i j)

set_option maxHeartbeats 2000000

/-- **Upper pure-mode reversed first variation.** -/
theorem snd_det_upperPureLockedReverseDualPencil
    (V ell k : K) :
    TrivSqZeroExt.snd (upperPureLockedReverseDualPencil V ell k).det =
      4 * V * (V + 1) * ell * (ell + 1) * k ^ 3 * (k - 1) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [upperPureLockedReverseDualPencil,
    upperPureDoubleRootMomentCore, lockedDoubleRootMomentCore,
    staircaseLogDirection, lineMomentHessian,
    rankThreeLogBaseExponent, rankThreeLogDirection,
    Matrix.det_fin_three, Fin.succAbove]
  ring

/-- Normalized value at `X=2 alpha` of a lower pure interior mode
`j+2=k`, whose translated multiplicity is `k-1`. -/
def lowerPureDoubleRootMomentCore
    (V k : K) : Matrix (Fin 4) (Fin 4) K :=
  lineMomentHessian
    (rankThreeLogBaseExponent k (k - 1) (2 * V * (k - 1)))
    (staircaseLogDirection V)
    1 (2 * (k - 1)) (2 * (k - 1) * (2 * (k - 1) - 1))

/-- Normalized primitive-highest endpoint at `X=2 alpha`, after multiplying
its affine profile by `n`. -/
def highestDoubleRootMomentCore
    (V n : K) : Matrix (Fin 4) (Fin 4) K :=
  lineMomentHessian
    (rankThreeLogBaseExponent n 1 (V * n))
    (staircaseLogDirection V)
    (n + 1) (2 * n) (2 * n)

/-- Dual-number pencil with the lower pure interior mode as constant part and
the primitive-highest endpoint as first variation. -/
def lowerPureHighestReverseDualPencil
    (V n k : K) : Matrix (Fin 4) (Fin 4) (DualNumber K) :=
  fun i j =>
    (lowerPureDoubleRootMomentCore V k i j,
      highestDoubleRootMomentCore V n i j)

/-- **Lower pure-mode reversed first variation.** -/
theorem snd_det_lowerPureHighestReverseDualPencil
    (V n k : K) :
    TrivSqZeroExt.snd (lowerPureHighestReverseDualPencil V n k).det =
      4 * V * n * (V + 1) * (k - 2) * (k - 1) ^ 3 * (n - 1) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [lowerPureHighestReverseDualPencil,
    lowerPureDoubleRootMomentCore, highestDoubleRootMomentCore,
    staircaseLogDirection, lineMomentHessian,
    rankThreeLogBaseExponent, rankThreeLogDirection,
    Matrix.det_fin_three, Fin.succAbove]
  ring

end

end HC4.Polynomial
