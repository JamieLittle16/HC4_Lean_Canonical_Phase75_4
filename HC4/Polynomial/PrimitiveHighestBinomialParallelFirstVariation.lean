import HC4.Polynomial.LockedBinomialParallelFirstVariation
import Mathlib.Algebra.DualNumber
import Mathlib.Tactic

/-!
# Parallel first variation of the primitive highest binomial

The locked-end first-variation calculation has a highest-end companion.  The
primitive highest slice has affine-line exponent data

    (0,n,1,V*n) + t (1,-1,-1,-V)

and affine coefficient profile `a + b*T`.  A lower parallel staircase layer
has exponent data

    (0,k,j+1,V*(k+j)) + t (1,-1,-1,-V)

with arbitrary profile `phi`.

The nilpotent coefficient of the determinant factors as

    V(V+1) * L * T^2 * affineTwoRootEulerOperator (a*n) (b*(n-1)) j phi,

where

    L = a*n + b*(n-1)*T.

Thus the first deformation away from the primitive highest slice is supported,
after translation to the root of `L`, only in the adjacent modes `j,j+1`.
This is the exact highest-end dual of `LockedBinomialParallelFirstVariation`.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Polynomial moment Hessian of the primitive highest binomial. -/
noncomputable def primitiveHighestBinomialMomentHessian
    (V n : ℕ) (a b : K) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  rankThreeAffinePolynomialMomentHessian
    n 1 (V * n) 1
    (-(1 : K)) (-(1 : K)) (-(V : K))
    (Polynomial.C a + Polynomial.C b * Polynomial.X)

/-- Dual-number pencil with primitive highest binomial constant part and one
lower parallel staircase layer as its nilpotent part. -/
noncomputable def primitiveHighestParallelFirstVariationDualPencil
    (V n k j : ℕ) (a b : K) (phi : Polynomial K) :
    Matrix (Fin 4) (Fin 4) (DualNumber (Polynomial K)) :=
  fun r s =>
    (primitiveHighestBinomialMomentHessian V n a b r s,
      parallelStaircaseMomentHessian V k j phi r s)

set_option maxHeartbeats 2000000

/-- **Exact primitive-highest first-variation factorisation.**

The pair degree `k` of the lower layer cancels.  The transverse staircase
height `j` becomes the lower indicial root of the affine two-root operator. -/
theorem snd_det_primitiveHighestParallelFirstVariationDualPencil
    (V n k j : ℕ) (hn : 2 ≤ n) (a b : K) (phi : Polynomial K) :
    TrivSqZeroExt.snd
        (primitiveHighestParallelFirstVariationDualPencil
          V n k j a b phi).det =
      Polynomial.C ((V : K) * ((V : K) + 1)) *
        affineEulerLinear
          (a * (n : K)) (b * ((n : K) - 1)) *
        Polynomial.X ^ 2 *
        affineTwoRootEulerOperator
          (a * (n : K)) (b * ((n : K) - 1)) j phi := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [primitiveHighestParallelFirstVariationDualPencil,
    primitiveHighestBinomialMomentHessian, parallelStaircaseMomentHessian,
    rankThreeAffinePolynomialMomentHessian_apply,
    rankThreeLogBaseExponent, rankThreeLogDirection,
    Matrix.det_fin_three, Fin.succAbove,
    affineTwoRootEulerOperator, affineEulerLinear,
    eulerDerivative]
  push_cast
  ring_nf
  have hCtwo : Polynomial.C (2 : K) = (2 : Polynomial K) := by
    calc
      Polynomial.C (2 : K) = Polynomial.C ((1 : K) + 1) := by congr 1 <;> ring
      _ = Polynomial.C (1 : K) + Polynomial.C 1 := by rw [Polynomial.C_add]
      _ = (1 : Polynomial K) + 1 := by simp
      _ = 2 := by ring
  rw [hCtwo]
  ring

/-- Vanishing first variation at the primitive highest binomial forces the
highest-end affine two-root equation. -/
theorem affineTwoRootEulerOperator_eq_zero_of_primitiveHighestParallel_snd_det_eq_zero
    (V n k j : ℕ)
    (hV : 0 < V) (hn : 2 ≤ n)
    (a b : K) (_ha : a ≠ 0) (hb : b ≠ 0)
    (phi : Polynomial K)
    (hdet :
      TrivSqZeroExt.snd
        (primitiveHighestParallelFirstVariationDualPencil
          V n k j a b phi).det = 0) :
    affineTwoRootEulerOperator
      (a * (n : K)) (b * ((n : K) - 1)) j phi = 0 := by
  rw [snd_det_primitiveHighestParallelFirstVariationDualPencil
    V n k j hn a b phi] at hdet
  have hVK : (V : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hV)
  have hV1Nat : V + 1 ≠ 0 := by omega
  have hV1Cast : ((V + 1 : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr hV1Nat
  have hV1K : (V : K) + 1 ≠ 0 := by
    simpa [Nat.cast_add] using hV1Cast
  have hnK : (n : K) ≠ 1 := by
    intro h
    have hn1 : n = 1 := by exact_mod_cast h
    omega
  have hnsub : (n : K) - 1 ≠ 0 := sub_ne_zero.mpr hnK
  have hscalar :
      Polynomial.C ((V : K) * ((V : K) + 1)) ≠ (0 : Polynomial K) := by
    exact Polynomial.C_ne_zero.mpr (mul_ne_zero hVK hV1K)
  have hB : b * ((n : K) - 1) ≠ 0 := mul_ne_zero hb hnsub
  have hlinear :
      affineEulerLinear
        (a * (n : K)) (b * ((n : K) - 1)) ≠ 0 := by
    intro hz
    have hc := congrArg (fun p : Polynomial K => p.coeff 1) hz
    have hc' : b * ((n : K) - 1) = 0 := by
      simpa [affineEulerLinear, Polynomial.coeff_one] using hc
    exact hB hc'
  have hX2 : (Polynomial.X : Polynomial K) ^ 2 ≠ 0 :=
    pow_ne_zero 2 Polynomial.X_ne_zero
  rcases mul_eq_zero.mp hdet with hprefix | hop
  · rcases mul_eq_zero.mp hprefix with hprefix' | hX
    · rcases mul_eq_zero.mp hprefix' with hscalar0 | hlinear0
      · exact (hscalar hscalar0).elim
      · exact (hlinear hlinear0).elim
    · exact (hX2 hX).elim
  · exact hop

end

end HC4.Polynomial
