import HC4.Polynomial.AffineEulerTwoRootRigidity
import HC4.Polynomial.RankThreeAffineMomentRealisation
import HC4.Polynomial.LockedBinomialParallelFirstVariation
import Mathlib.Algebra.DualNumber
import Mathlib.Tactic

/-!
# Parallel first variation from the primitive highest binomial

This is the endpoint-dual companion to `LockedBinomialParallelFirstVariation`.
The primitive highest pair has affine-line exponent data

    (0, n, 1, V*n) + t (1,-1,-1,-V)

and affine coefficient profile `c + d T`.  A lower parallel staircase fibre of
pair degree `k` and height `j` has exponent data

    (0, k, j+1, V*(k+j)) + t (1,-1,-1,-V)

with arbitrary profile `phi(T)`.

The nilpotent determinant coefficient of the corresponding dual-number pencil
factors as

    V(V+1) * L_top * T^2 * affineTwoRootEulerOperator(C,D,j,phi),

where

    C = c*n,   D = d*(n-1),   L_top = C + D*T.

Thus the pair degree `k` cancels completely.  This is the precise dual of the
locked-end calculation, where the height cancels and the roots are `k-1,k`.
-/

namespace HC4.Polynomial

noncomputable section

open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Polynomial moment Hessian of the literal primitive highest pair. -/
noncomputable def highestBinomialMomentHessian
    (V n : ℕ) (c d : K) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  rankThreeAffinePolynomialMomentHessian
    n 1 (V * n) 1
    (-(1 : K)) (-(1 : K)) (-(V : K))
    (Polynomial.C c + Polynomial.C d * Polynomial.X)

/-- Dual-number pencil whose constant component is the highest primitive pair
and whose nilpotent component is a lower parallel staircase fibre. -/
noncomputable def highestParallelFirstVariationDualPencil
    (V n k j : ℕ) (c d : K) (phi : Polynomial K) :
    Matrix (Fin 4) (Fin 4) (DualNumber (Polynomial K)) :=
  fun r s =>
    (highestBinomialMomentHessian V n c d r s,
      parallelStaircaseMomentHessian V k j phi r s)

set_option maxHeartbeats 2000000

/-- **Exact highest-binomial first-variation factorisation.**

The lower fibre's pair degree `k` disappears.  The remaining operator has the
adjacent indicial roots `j,j+1`, i.e. it measures distance from the highest
endpoint in the transverse staircase coordinate. -/
theorem snd_det_highestParallelFirstVariationDualPencil
    (V n k j : ℕ) (hn : 1 ≤ n) (c d : K) (phi : Polynomial K) :
    TrivSqZeroExt.snd
        (highestParallelFirstVariationDualPencil
          V n k j c d phi).det =
      Polynomial.C ((V : K) * ((V : K) + 1)) *
        affineEulerLinear
          (c * (n : K)) (d * ((n - 1 : ℕ) : K)) *
        Polynomial.X ^ 2 *
        affineTwoRootEulerOperator
          (c * (n : K)) (d * ((n - 1 : ℕ) : K))
          j phi := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [highestParallelFirstVariationDualPencil,
    highestBinomialMomentHessian, parallelStaircaseMomentHessian,
    rankThreeAffinePolynomialMomentHessian_apply,
    rankThreeLogBaseExponent, rankThreeLogDirection,
    Matrix.det_fin_three, Fin.succAbove,
    affineTwoRootEulerOperator, affineEulerLinear,
    eulerDerivative]
  push_cast
  rw [Nat.cast_sub hn]
  ring_nf
  have hCtwo : Polynomial.C (2 : K) = (2 : Polynomial K) := by
    calc
      Polynomial.C (2 : K) = Polynomial.C ((1 : K) + 1) := by congr 1 <;> ring
      _ = Polynomial.C (1 : K) + Polynomial.C 1 := by rw [Polynomial.C_add]
      _ = (1 : Polynomial K) + 1 := by simp
      _ = 2 := by ring
  rw [hCtwo]
  ring

/-- Vanishing highest-end first variation forces the dual affine two-root Euler
operator, provided the highest outside coefficient and the non-unit parameters
are nonzero. -/
theorem affineTwoRootEulerOperator_eq_zero_of_highestParallel_snd_det_eq_zero
    (V n k j : ℕ)
    (hV : 0 < V) (hn : 2 ≤ n)
    (c d : K) (_hc : c ≠ 0) (hd : d ≠ 0)
    (phi : Polynomial K)
    (hdet :
      TrivSqZeroExt.snd
        (highestParallelFirstVariationDualPencil
          V n k j c d phi).det = 0) :
    affineTwoRootEulerOperator
      (c * (n : K)) (d * ((n - 1 : ℕ) : K)) j phi = 0 := by
  have hn1 : 1 ≤ n := by omega
  rw [snd_det_highestParallelFirstVariationDualPencil
    V n k j hn1 c d phi] at hdet
  have hVK : (V : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hV)
  have hV1Nat : V + 1 ≠ 0 := by omega
  have hV1Cast : ((V + 1 : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr hV1Nat
  have hV1K : (V : K) + 1 ≠ 0 := by
    simpa [Nat.cast_add] using hV1Cast
  have hnsub : n - 1 ≠ 0 := by omega
  have hnsubK : ((n - 1 : ℕ) : K) ≠ 0 :=
    Nat.cast_ne_zero.mpr hnsub
  have hscalar :
      Polynomial.C ((V : K) * ((V : K) + 1)) ≠ (0 : Polynomial K) := by
    exact Polynomial.C_ne_zero.mpr (mul_ne_zero hVK hV1K)
  have hD : d * ((n - 1 : ℕ) : K) ≠ 0 := mul_ne_zero hd hnsubK
  have hlinear :
      affineEulerLinear
        (c * (n : K)) (d * ((n - 1 : ℕ) : K)) ≠ 0 := by
    intro hz
    have hc1 := congrArg (fun p : Polynomial K => p.coeff 1) hz
    have hc1' : d * ((n - 1 : ℕ) : K) = 0 := by
      simpa [affineEulerLinear, Polynomial.coeff_one] using hc1
    exact hD hc1'
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
