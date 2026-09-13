import HC4.Polynomial.AffineEulerTwoRootRigidity
import HC4.Polynomial.RankThreeAffineMomentRealisation
import Mathlib.Algebra.DualNumber
import Mathlib.Tactic

/-!
# Parallel first variation of a locked rank-three binomial

This file isolates the only symbolic determinant calculation needed by the
`V > 1` planar-contact interior elimination.

The locked special fibre has affine-line exponent data

    (0, 1, ell+1, V(ell+1)) + t (1,-1,-1,-V)

and affine coefficient profile `a + b T`.  A parallel staircase layer of pair
degree `k` and height `j` has exponent data

    (0, k, j+1, V(k+j)) + t (1,-1,-1,-V)

with arbitrary polynomial profile `phi(T)`.

Put the locked moment Hessian in the constant component of the dual numbers
and the parallel layer in the nilpotent component.  The nilpotent coefficient
of its determinant factors as

    V(V+1) * L * T^2 * affineTwoRootEulerOperator(A,B,k-1,phi),

where

    A = a(ell+1),   B = b ell,
    L = A + B T.

The staircase height `j` cancels completely.  Thus, whenever the first
variation vanishes and the literal locked coefficients are nonzero, the
existing affine two-root rigidity theorem applies directly.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Polynomial moment Hessian of the literal locked pair. -/
noncomputable def lockedBinomialMomentHessian
    (V ell : ℕ) (a b : K) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  rankThreeAffinePolynomialMomentHessian
    1 (ell + 1) (V * (ell + 1)) 1
    (-(1 : K)) (-(1 : K)) (-(V : K))
    (Polynomial.C a + Polynomial.C b * Polynomial.X)

/-- Polynomial moment Hessian of a parallel staircase fibre. -/
noncomputable def parallelStaircaseMomentHessian
    (V k j : ℕ) (phi : Polynomial K) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  rankThreeAffinePolynomialMomentHessian
    k (j + 1) (V * (k + j)) 1
    (-(1 : K)) (-(1 : K)) (-(V : K)) phi

/-- Dual-number pencil whose constant term is the locked Hessian and whose
nilpotent term is one parallel staircase Hessian layer. -/
noncomputable def lockedParallelFirstVariationDualPencil
    (V ell k j : ℕ) (a b : K) (phi : Polynomial K) :
    Matrix (Fin 4) (Fin 4) (DualNumber (Polynomial K)) :=
  fun r s =>
    (lockedBinomialMomentHessian V ell a b r s,
      parallelStaircaseMomentHessian V k j phi r s)

/-- **Exact locked-binomial first-variation factorisation.**

The height `j` of the parallel staircase disappears from the determinant
coefficient.  The remaining differential operator is exactly the previously
formalised affine two-root Euler operator with adjacent roots `k-1,k`. -/
set_option maxHeartbeats 2000000 in
theorem snd_det_lockedParallelFirstVariationDualPencil
    (V ell k j : ℕ) (hk : 1 ≤ k) (a b : K) (phi : Polynomial K) :
    TrivSqZeroExt.snd
        (lockedParallelFirstVariationDualPencil
          V ell k j a b phi).det =
      Polynomial.C ((V : K) * ((V : K) + 1)) *
        affineEulerLinear
          (a * ((ell : K) + 1)) (b * (ell : K)) *
        Polynomial.X ^ 2 *
        affineTwoRootEulerOperator
          (a * ((ell : K) + 1)) (b * (ell : K))
          (k - 1) phi := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [lockedParallelFirstVariationDualPencil,
    lockedBinomialMomentHessian, parallelStaircaseMomentHessian,
    rankThreeAffinePolynomialMomentHessian_apply,
    rankThreeLogBaseExponent, rankThreeLogDirection,
    Matrix.det_fin_three, Fin.succAbove,
    affineTwoRootEulerOperator, affineEulerLinear,
    eulerDerivative, DualNumber.snd_mul]
  push_cast
  have hkcast : (((k - 1 : ℕ) : K)) = (k : K) - 1 := by
    rw [Nat.cast_sub hk]
    norm_num
  rw [hkcast]
  ring

/-- Vanishing first variation forces the affine two-root Euler equation as soon
as the locked endpoint coefficient and the non-unit staircase parameters are
nonzero. -/
theorem affineTwoRootEulerOperator_eq_zero_of_lockedParallel_snd_det_eq_zero
    (V ell k j : ℕ)
    (hV : 0 < V) (hell : 0 < ell) (hk : 1 ≤ k)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (phi : Polynomial K)
    (hdet :
      TrivSqZeroExt.snd
        (lockedParallelFirstVariationDualPencil
          V ell k j a b phi).det = 0) :
    affineTwoRootEulerOperator
      (a * ((ell : K) + 1)) (b * (ell : K))
      (k - 1) phi = 0 := by
  rw [snd_det_lockedParallelFirstVariationDualPencil
    V ell k j hk a b phi] at hdet
  have hVK : (V : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hV)
  have hV1K : (V : K) + 1 ≠ 0 := by
    have : (0 : K) < (V : K) + 1 := by positivity
    exact ne_of_gt this
  have hellK : (ell : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hell)
  have hscalar :
      Polynomial.C ((V : K) * ((V : K) + 1)) ≠ (0 : Polynomial K) := by
    exact Polynomial.C_ne_zero.mpr (mul_ne_zero hVK hV1K)
  have hB : b * (ell : K) ≠ 0 := mul_ne_zero hb hellK
  have hlinear :
      affineEulerLinear
        (a * ((ell : K) + 1)) (b * (ell : K)) ≠ 0 := by
    intro hz
    have hc := congrArg (fun p : Polynomial K => p.coeff 1) hz
    simp [affineEulerLinear, hB] at hc
  have hX2 : (Polynomial.X : Polynomial K) ^ 2 ≠ 0 :=
    pow_ne_zero 2 Polynomial.X_ne_zero
  rcases mul_eq_zero.mp hdet with hleft | hop
  · rcases mul_eq_zero.mp hleft with hscalar0 | hrest
    · exact (hscalar hscalar0).elim
    · rcases mul_eq_zero.mp hrest with hlinear0 | hX
      · exact (hlinear hlinear0).elim
      · exact (hX2 hX).elim
  · exact hop

end

end HC4.Polynomial
