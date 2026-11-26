module

public import HC4.Polynomial.RationalCharacteristicRankOneSourceChart

/-!
# Radial source equation for a self-adjoint rank-one Jacobian

For N = u v^T and N^T H = H N, every vector r annihilated by v
satisfies u^T H r = 0, provided v has a nonzero component.
In the chart t = x/y, the normalized row (1,-t,0) annihilates the
source radial vector. The contraction is the directional derivative
of Euler(f)-f. Thus the source Hessian identity gives an evaluated
polynomial relation whose homogeneous coefficients encode exactly
the chart recurrence.

The conversion of the evaluated relation to chart coefficients is
separate. No independent recurrence is assumed in the theorems here.
-/

@[expose] public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

section MatrixAlgebra

variable {F ι : Type*} [Field F] [Fintype ι] [DecidableEq ι]

/-- A rank-one self-adjoint operator contracts to zero against
any vector in its right kernel. No invertibility of H is needed. -/
theorem rankOne_selfAdjoint_radial_contraction
    (H N : Matrix ι ι F) (u v r : ι → F)
    (hN : ∀ i j, N i j = u i * v j)
    (hself : N.transpose * H = H * N)
    (k : ι) (hk : v k ≠ 0) (hr : v ⬝ᵥ r = 0) :
    u ⬝ᵥ (H *ᵥ r) = 0 := by
  classical
  have hn : N *ᵥ r = 0 := by
    funext i
    change (∑ j : ι, N i j * r j) = 0
    simp only [hN, mul_assoc, ← Finset.mul_sum]
    change u i * (v ⬝ᵥ r) = 0
    rw [hr, mul_zero]
  have hleft : N.transpose *ᵥ (H *ᵥ r) = 0 := by
    rw [Matrix.mulVec_mulVec, hself, ← Matrix.mulVec_mulVec, hn,
      Matrix.mulVec_zero]
  have h := congrFun hleft k
  change (∑ i : ι, N i k * (H *ᵥ r) i) = 0 at h
  simp only [hN] at h
  have hfactor : (∑ i : ι, u i * v k * (H *ᵥ r) i) =
      v k * (u ⬝ᵥ (H *ᵥ r)) := by
    rw [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  rw [hfactor] at h
  exact (mul_eq_zero.mp h).resolve_left hk

end MatrixAlgebra

variable {K : Type*} [Field K]

namespace RationalCharacteristicRankOneRadial

abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev E (K : Type*) [Field K] := FractionRing (B K)

end RationalCharacteristicRankOneRadial

open RationalCharacteristicRankOneRadial (B E)

/-- The source radial vector in the fraction field. -/
def rankOne_sourceRadial : Fin 3 → E K :=
  fun i => algebraMap (B K) (E K) (X i)

/-- The normalized affine-ratio parameter and its scaled gradient. -/
def rankOne_normalizedParameter : E K :=
  rankOne_sourceRadial (K := K) 0 / rankOne_sourceRadial (K := K) 1

def rankOne_normalizedRow : Fin 3 → E K :=
  ![1, -rankOne_normalizedParameter, 0]

theorem rankOne_sourceRadial_y_ne_zero :
    rankOne_sourceRadial (K := K) 1 ≠ 0 := by
  change algebraMap (B K) (E K) (X (1 : Fin 3)) ≠ 0
  intro h
  have hz : (X (1 : Fin 3) : B K) = 0 := by
    apply IsFractionRing.injective (B K) (E K)
    simpa only [map_zero] using h
  exact MvPolynomial.X_ne_zero (R := K) (1 : Fin 3) hz

/-- The normalized parameter is constant along radial directions. -/
theorem rankOne_normalizedRow_radial_zero :
    rankOne_normalizedRow (K := K) ⬝ᵥ rankOne_sourceRadial = 0 := by
  have hy := rankOne_sourceRadial_y_ne_zero (K := K)
  change (∑ i : Fin 3, rankOne_normalizedRow (K := K) i *
    rankOne_sourceRadial i) = 0
  simp [Fin.sum_univ_three, rankOne_normalizedRow, rankOne_normalizedParameter,
    div_mul_cancel₀ _ hy]

/-- In the normalized chart the rank-one factorization of N and
self-adjointness of the actual polynomial Hessian yield a radial
contraction identity over the fraction field. -/
theorem rankOne_normalized_radialHessian_zero
    (f : B K) (N : Matrix (Fin 3) (Fin 3) (E K)) (u : Fin 3 → E K)
    (hN : ∀ i j, N i j = u i * rankOne_normalizedRow j)
    (hself : N.transpose * (hessian f).map (algebraMap (B K) (E K)) =
      (hessian f).map (algebraMap (B K) (E K)) * N) :
    u ⬝ᵥ ((hessian f).map (algebraMap (B K) (E K)) *ᵥ
      rankOne_sourceRadial) = 0 := by
  apply rankOne_selfAdjoint_radial_contraction _ N u
    rankOne_normalizedRow rankOne_sourceRadial hN hself (0 : Fin 3)
  · simp [rankOne_normalizedRow]
  · exact rankOne_normalizedRow_radial_zero

variable [CharZero K]

/-- The radial Hessian product is the gradient of Euler(f)-f.
This is the polynomial identity underlying the homogeneous
coefficient recurrence. -/
theorem rankOne_radialHessian_eq_eulerGradient
    (f : B K) (i : Fin 3) :
    (∑ j : Fin 3, hessian f i j * X j) =
      pderiv i (transverseEuler f - f) := by
  classical
  rw [map_sub]
  unfold transverseEuler
  rw [map_sum]
  have h (j : Fin 3) : pderiv i (X j * pderiv j f) =
      X j * pderiv j (pderiv i f) + pderiv i (X j) * pderiv j f := by
    rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul,
      HC4.Newton.pderiv_comm_backport i j]
    ring
  simp only [h, Finset.sum_add_distrib]
  have hs : (∑ j : Fin 3, pderiv i (X j) * pderiv j f) = pderiv i f := by
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      rw [pderiv_X_of_ne hj, zero_mul]
    · simp
  rw [hs, add_sub_cancel_right]
  apply Finset.sum_congr rfl
  intro j _
  rw [hessian_apply, mul_comm]

/-- Fraction-field self-adjointness in the normalized chart gives
the source Euler-gradient equation. -/
theorem rankOne_normalized_eulerGradient_zero
    (f : B K) (N : Matrix (Fin 3) (Fin 3) (E K)) (u : Fin 3 → E K)
    (hN : ∀ i j, N i j = u i * rankOne_normalizedRow j)
    (hself : N.transpose * (hessian f).map (algebraMap (B K) (E K)) =
      (hessian f).map (algebraMap (B K) (E K)) * N) :
    (∑ i : Fin 3, u i * algebraMap (B K) (E K)
      (pderiv i (transverseEuler f - f))) = 0 := by
  have hr := rankOne_normalized_radialHessian_zero f N u hN hself
  have he (i : Fin 3) :
      ((hessian f).map (algebraMap (B K) (E K)) *ᵥ
        rankOne_sourceRadial) i =
      algebraMap (B K) (E K) (pderiv i (transverseEuler f - f)) := by
    rw [← rankOne_radialHessian_eq_eulerGradient]
    simp [Matrix.mulVec, dotProduct, rankOne_sourceRadial, map_sum, map_mul]
  change (∑ i : Fin 3, u i *
    ((hessian f).map (algebraMap (B K) (E K)) *ᵥ rankOne_sourceRadial) i) = 0 at hr
  simpa only [he] using hr

end
end HC4.Polynomial.RankThreeCubic
