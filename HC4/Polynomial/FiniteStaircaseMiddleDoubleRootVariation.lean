import HC4.Polynomial.FiniteStaircasePureModeReversedFirstVariation
import Mathlib.Algebra.DualNumber
import Mathlib.Tactic

/-!
# Middle one-fibre variations at the common affine root

On the middle diagonal `j+1=k`, evaluation at twice the common affine root
turns the two translated modes `X^(k-1)` and `X^k` into two explicit constant
moment cores.  This file records the endpoint second variations for their
linear combination and the reversed first variations of the pure top mode.

These are state-free ring identities.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

universe u
variable {K : Type u} [CommRing K]

/-- Normalized `X^(k-1)` middle-mode moment core at twice the common root. -/
def middleLowerDoubleRootMomentCore
    (V k : K) : Matrix (Fin 4) (Fin 4) K :=
  lineMomentHessian
    (rankThreeLogBaseExponent k k (V * (2 * k - 1)))
    (staircaseLogDirection V)
    1 (2 * (k - 1)) (2 * (k - 1) * (2 * (k - 1) - 1))

/-- Normalized `X^k` central middle-mode moment core at twice the common root. -/
def middleUpperDoubleRootMomentCore
    (V k : K) : Matrix (Fin 4) (Fin 4) K :=
  lineMomentHessian
    (rankThreeLogBaseExponent k k (V * (2 * k - 1)))
    (staircaseLogDirection V)
    1 (2 * k) (2 * k * (2 * k - 1))

/-- Evaluated middle interior matrix with arbitrary lower/top mode scalars. -/
def middleTwoModeDoubleRootMomentCore
    (V k u v : K) : Matrix (Fin 4) (Fin 4) K :=
  u • middleLowerDoubleRootMomentCore V k +
    v • middleUpperDoubleRootMomentCore V k

/-- Second jet based at the normalized highest endpoint. -/
def middleHighestSecondJet
    (V n k a u v : K) :
    Matrix (Fin 4) (Fin 4) (DualNumber (DualNumber K)) :=
  let A := a • highestDoubleRootMomentCore V n
  let B := middleTwoModeDoubleRootMomentCore V k u v
  fun i j => ((A i j, B i j), (B i j, 0))

set_option maxHeartbeats 3000000

/-- **Highest-side middle second variation.** -/
theorem snd_snd_det_middleHighestSecondJet
    (V n k a u v : K) :
    TrivSqZeroExt.snd
      (TrivSqZeroExt.snd (middleHighestSecondJet V n k a u v).det) =
      8 * V * (V + 1) * a ^ 2 * n ^ 2 * (n - 1) ^ 2 *
        (k - 1) * u *
        (((k * n + k - n - 3) * u) + 2 * k * v) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [middleHighestSecondJet, middleTwoModeDoubleRootMomentCore,
    middleLowerDoubleRootMomentCore, middleUpperDoubleRootMomentCore,
    highestDoubleRootMomentCore, staircaseLogDirection,
    lineMomentHessian, rankThreeLogBaseExponent, rankThreeLogDirection,
    Matrix.det_fin_three, Fin.succAbove]
  ring

/-- Second jet based at the normalized locked endpoint. -/
def middleLockedSecondJet
    (V ell k b u v : K) :
    Matrix (Fin 4) (Fin 4) (DualNumber (DualNumber K)) :=
  let A := b • lockedDoubleRootMomentCore V ell
  let B := middleTwoModeDoubleRootMomentCore V k u v
  fun i j => ((A i j, B i j), (B i j, 0))

/-- **Locked-side middle second variation.** -/
theorem snd_snd_det_middleLockedSecondJet
    (V ell k b u v : K) :
    TrivSqZeroExt.snd
      (TrivSqZeroExt.snd (middleLockedSecondJet V ell k b u v).det) =
      8 * V * (V + 1) * b ^ 2 * ell ^ 2 * (ell + 1) ^ 2 *
        (k - 1) * u *
        (((ell * k - ell + 2 * k - 4) * u) + 2 * k * v) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [middleLockedSecondJet, middleTwoModeDoubleRootMomentCore,
    middleLowerDoubleRootMomentCore, middleUpperDoubleRootMomentCore,
    lockedDoubleRootMomentCore, staircaseLogDirection,
    lineMomentHessian, rankThreeLogBaseExponent, rankThreeLogDirection,
    Matrix.det_fin_three, Fin.succAbove]
  ring

/-- Reversed first variation of the pure central top mode by the highest
endpoint.  Equivalently this is the cubic coefficient of the corresponding
ordinary linear pencil. -/
def middleUpperHighestReverseDualPencil
    (V n k a v : K) : Matrix (Fin 4) (Fin 4) (DualNumber K) :=
  fun i j =>
    (v * middleUpperDoubleRootMomentCore V k i j,
      a * highestDoubleRootMomentCore V n i j)

/-- **Central/highest cubic obstruction.** -/
theorem snd_det_middleUpperHighestReverseDualPencil
    (V n k a v : K) :
    TrivSqZeroExt.snd
      (middleUpperHighestReverseDualPencil V n k a v).det =
      4 * V * (V + 1) * n * (n - 1) * (k - 1) * k ^ 3 *
        a * v ^ 3 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [middleUpperHighestReverseDualPencil,
    middleUpperDoubleRootMomentCore, highestDoubleRootMomentCore,
    staircaseLogDirection, lineMomentHessian,
    rankThreeLogBaseExponent, rankThreeLogDirection,
    Matrix.det_fin_three, Fin.succAbove]
  ring

/-- Reversed first variation of the pure central top mode by the locked
endpoint. -/
def middleUpperLockedReverseDualPencil
    (V ell k b v : K) : Matrix (Fin 4) (Fin 4) (DualNumber K) :=
  fun i j =>
    (v * middleUpperDoubleRootMomentCore V k i j,
      b * lockedDoubleRootMomentCore V ell i j)

/-- **Central/locked cubic obstruction.** -/
theorem snd_det_middleUpperLockedReverseDualPencil
    (V ell k b v : K) :
    TrivSqZeroExt.snd
      (middleUpperLockedReverseDualPencil V ell k b v).det =
      4 * V * (V + 1) * ell * (ell + 1) * (k - 1) * k ^ 3 *
        b * v ^ 3 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [middleUpperLockedReverseDualPencil,
    middleUpperDoubleRootMomentCore, lockedDoubleRootMomentCore,
    staircaseLogDirection, lineMomentHessian,
    rankThreeLogBaseExponent, rankThreeLogDirection,
    Matrix.det_fin_three, Fin.succAbove]
  ring

end

end HC4.Polynomial
