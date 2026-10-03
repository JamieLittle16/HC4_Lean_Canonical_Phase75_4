import HC4.Polynomial.FiniteStaircaseTranslatedPureModeEvaluation
import HC4.Polynomial.LockedBinomialParallelFirstVariation
import HC4.Polynomial.HighestBinomialParallelFirstVariation
import Mathlib.Tactic

/-!
# Endpoint moment matrices at twice the common affine root

The one-fibre coupling proves that the locked and primitive-highest affine
forms have the same root `alpha`.  Evaluating at `X=2 alpha` normalizes both
endpoint moment matrices to the constant cores used by the reversed
first-variation calculation.

For the locked endpoint

    a(ell+1) + b ell alpha = 0,

and the scalar is `b alpha/(ell+1)`.  For the highest endpoint

    c n + d(n-1) alpha = 0,

and the scalar is `d alpha/n`.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Locked affine endpoint at twice its weighted affine root. -/
theorem eval_two_mul_lockedBinomialMomentHessian_of_root
    (V ell : ℕ) (a b alpha : K)
    (hell : 0 < ell)
    (hroot :
      a * ((ell : K) + 1) + b * (ell : K) * alpha = 0) :
    (fun i j => Polynomial.eval (2 * alpha)
      (lockedBinomialMomentHessian V ell a b i j)) =
      (b * alpha / ((ell : K) + 1)) •
        lockedDoubleRootMomentCore (V : K) (ell : K) := by
  let lam : K := b * alpha / ((ell : K) + 1)
  let phi : Polynomial K := Polynomial.C a + Polynomial.C b * Polynomial.X
  have hdenNat : ell + 1 ≠ 0 := by omega
  have hden : ((ell : K) + 1) ≠ 0 := by
    have : (((ell + 1 : ℕ) : K)) ≠ 0 := Nat.cast_ne_zero.mpr hdenNat
    simpa [Nat.cast_add] using this
  have h0 : Polynomial.eval (2 * alpha) phi = lam * ((ell : K) + 2) := by
    dsimp [phi, lam]
    simp only [Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
    field_simp [hden]
    linear_combination hroot
  have h1 : Polynomial.eval (2 * alpha) (eulerDerivative phi) =
      lam * (2 * ((ell : K) + 1)) := by
    dsimp [phi, lam]
    simp [eulerDerivative]
    field_simp [hden]
    ring
  have h2 : Polynomial.eval (2 * alpha)
      (eulerDerivative (eulerDerivative phi)) =
      lam * (2 * ((ell : K) + 1)) := by
    dsimp [phi, lam]
    simp [eulerDerivative]
    field_simp [hden]
    ring
  have heval := eval_rankThreeAffinePolynomialMomentHessian
    (K := K) 1 (ell + 1) (V * (ell + 1)) 1
    (-1 : K) (-1 : K) (-(V : K)) phi (2 * alpha)
  change
    (fun i j => Polynomial.eval (2 * alpha)
      (rankThreeAffinePolynomialMomentHessian
        1 (ell + 1) (V * (ell + 1)) 1
        (-1 : K) (-1 : K) (-(V : K)) phi i j)) = _
  rw [heval, h0, h1, h2]
  apply Matrix.ext
  intro i j
  simp [lockedDoubleRootMomentCore, staircaseLogDirection,
    lineMomentHessian, lam]
  ring

/-- Primitive-highest affine endpoint at twice its weighted affine root. -/
theorem eval_two_mul_highestBinomialMomentHessian_of_root
    (V n : ℕ) (c d alpha : K)
    (hn : 1 ≤ n)
    (hroot :
      c * (n : K) + d * ((n - 1 : ℕ) : K) * alpha = 0) :
    (fun i j => Polynomial.eval (2 * alpha)
      (highestBinomialMomentHessian V n c d i j)) =
      (d * alpha / (n : K)) •
        highestDoubleRootMomentCore (V : K) (n : K) := by
  let lam : K := d * alpha / (n : K)
  let phi : Polynomial K := Polynomial.C c + Polynomial.C d * Polynomial.X
  have hn0 : n ≠ 0 := by omega
  have hnK : (n : K) ≠ 0 := Nat.cast_ne_zero.mpr hn0
  have hnsubCast : ((n - 1 : ℕ) : K) = (n : K) - 1 := by
    rw [Nat.cast_sub hn]
    simp
  have h0 : Polynomial.eval (2 * alpha) phi = lam * ((n : K) + 1) := by
    dsimp [phi, lam]
    simp only [Polynomial.eval_add, Polynomial.eval_C,
      Polynomial.eval_mul, Polynomial.eval_X]
    rw [hnsubCast] at hroot
    field_simp [hnK]
    linear_combination hroot
  have h1 : Polynomial.eval (2 * alpha) (eulerDerivative phi) =
      lam * (2 * (n : K)) := by
    dsimp [phi, lam]
    simp [eulerDerivative]
    field_simp [hnK]
    ring
  have h2 : Polynomial.eval (2 * alpha)
      (eulerDerivative (eulerDerivative phi)) =
      lam * (2 * (n : K)) := by
    dsimp [phi, lam]
    simp [eulerDerivative]
    field_simp [hnK]
    ring
  have heval := eval_rankThreeAffinePolynomialMomentHessian
    (K := K) n 1 (V * n) 1
    (-1 : K) (-1 : K) (-(V : K)) phi (2 * alpha)
  change
    (fun i j => Polynomial.eval (2 * alpha)
      (rankThreeAffinePolynomialMomentHessian
        n 1 (V * n) 1
        (-1 : K) (-1 : K) (-(V : K)) phi i j)) = _
  rw [heval, h0, h1, h2]
  apply Matrix.ext
  intro i j
  simp [highestDoubleRootMomentCore, staircaseLogDirection,
    lineMomentHessian, lam]
  ring

end

end HC4.Polynomial
