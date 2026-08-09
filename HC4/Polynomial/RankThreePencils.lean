import HC4.Polynomial.MonomialHessian
import Mathlib.LinearAlgebra.Matrix.Determinant.Basic

/-!
# Exact rank-three binomial pencil identities

These are the two exact 4x4 determinant calculations used at the end of the
rank-three Newton-edge theorem.  They are deliberately isolated from the
logarithmic-ODE part so that the algebraic endpoint can be kernel checked
independently.

For `M(z) = z zᵀ - diag(z)`, the manuscript needs

* `v=(0,C,D,E)`, `u=(1,0,F,0)`:
  `det(M(v)+tM(u)) = C E F^2 (C+E-1) t^2`;
* `v=(0,1,C,D)`, `u=(1,0,E,F)`:
  `det(M(v)+tM(u)) = t^2 (ED-CF)^2`.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

/-- Hessian core for a coefficient-valued four-vector. -/
def vectorHessianCore {K : Type*} [CommRing K]
    (z : Fin 4 → K) : Matrix (Fin 4) (Fin 4) K :=
  Matrix.of fun i j => z i * z j - if i = j then z i else 0

/-- The sparse two-zero rank-three pencil occurring in the first terminal
binomial case. -/
def sparseRankThreePencil {K : Type*} [CommRing K]
    (C D E F t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, F * t, 0;
     0, C^2 - C, C * D, C * E;
     F * t, C * D, D^2 - D + t * (F^2 - F), D * E;
     0, C * E, D * E, E^2 - E]

/-- The explicit sparse matrix really is `M(v)+tM(u)`. -/
theorem sparseRankThreePencil_eq_core {K : Type*} [CommRing K]
    (C D E F t : K) :
    sparseRankThreePencil C D E F t =
      vectorHessianCore ![0, C, D, E] +
        t • vectorHessianCore ![1, 0, F, 0] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [sparseRankThreePencil, vectorHessianCore] <;> ring

/-- First exact rank-three determinant identity. -/
theorem det_sparseRankThreePencil {K : Type*} [CommRing K]
    (C D E F t : K) :
    (sparseRankThreePencil C D E F t).det =
      C * E * F^2 * (C + E - 1) * t^2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [sparseRankThreePencil, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- The one-zero rank-three pencil occurring in the final binomial case. -/
def oneZeroRankThreePencil {K : Type*} [CommRing K]
    (C D E F t : K) : Matrix (Fin 4) (Fin 4) K :=
  !![0, 0, E * t, F * t;
     0, 0, C, D;
     E * t, C, C^2 - C + t * (E^2 - E), C * D + E * F * t;
     F * t, D, C * D + E * F * t, D^2 - D + t * (F^2 - F)]

/-- The explicit one-zero matrix is again `M(v)+tM(u)`. -/
theorem oneZeroRankThreePencil_eq_core {K : Type*} [CommRing K]
    (C D E F t : K) :
    oneZeroRankThreePencil C D E F t =
      vectorHessianCore ![0, 1, C, D] +
        t • vectorHessianCore ![1, 0, E, F] := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [oneZeroRankThreePencil, vectorHessianCore] <;> ring

/-- Second exact rank-three determinant identity. -/
theorem det_oneZeroRankThreePencil {K : Type*} [CommRing K]
    (C D E F t : K) :
    (oneZeroRankThreePencil C D E F t).det =
      t^2 * (E * D - C * F)^2 := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [oneZeroRankThreePencil, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- If the second pencil is singular at one nonzero parameter in a domain,
its endpoint exponent pairs obey the cross-product relation `ED=CF`. -/
theorem cross_relation_of_oneZero_pencil_singular
    {K : Type*} [CommRing K] [IsDomain K]
    {C D E F t : K} (ht : t ≠ 0)
    (hzero : (oneZeroRankThreePencil C D E F t).det = 0) :
    E * D = C * F := by
  rw [det_oneZeroRankThreePencil] at hzero
  have ht2 : t^2 ≠ 0 := pow_ne_zero 2 ht
  have hsq : (E * D - C * F)^2 = 0 :=
    (mul_eq_zero.mp hzero).resolve_left ht2
  have hsq' : (E * D - C * F) * (E * D - C * F) = 0 := by
    simpa [pow_two] using hsq
  have hsub : E * D - C * F = 0 := mul_self_eq_zero.mp hsq'
  exact sub_eq_zero.mp hsub

/-- The cross-product relation from the singular one-zero pencil, together
with invariance of the two endpoint exponents, forces the corresponding two
grading weights to be positively proportional.  This is the division-free
form of the manuscript relation `w1 = lambda*w2`. -/
theorem weight_cross_relation_of_invariant_endpoints
    {K : Type*} [CommRing K]
    {C D E F w1 w2 w3 w4 : K}
    (hcross : E * D = C * F)
    (hv : w2 + C * w3 + D * w4 = 0)
    (hu : w1 + E * w3 + F * w4 = 0) :
    E * w2 = C * w1 := by
  linear_combination E * hv - C * hu - w4 * hcross

/-- For positive integer scale factors, the preceding cross relation forces
the two integer grading weights to have the same strict sign. -/
theorem same_sign_of_positive_weight_cross_relation
    {C E : ℕ} {w1 w2 : ℤ} (hC : 0 < C) (hE : 0 < E)
    (hcross : (E : ℤ) * w2 = (C : ℤ) * w1) :
    (0 < w1 ↔ 0 < w2) ∧ (w1 < 0 ↔ w2 < 0) := by
  have hCZ : (0 : ℤ) < (C : ℤ) := by exact_mod_cast hC
  have hEZ : (0 : ℤ) < (E : ℤ) := by exact_mod_cast hE
  constructor
  · constructor
    · intro hw1
      by_contra hn
      have hw2le : w2 ≤ 0 := le_of_not_gt hn
      have hlhs : (E : ℤ) * w2 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hEZ) hw2le
      rw [hcross] at hlhs
      exact (not_lt_of_ge hlhs) (mul_pos hCZ hw1)
    · intro hw2
      by_contra hn
      have hw1le : w1 ≤ 0 := le_of_not_gt hn
      have hrhs : (C : ℤ) * w1 ≤ 0 :=
        mul_nonpos_of_nonneg_of_nonpos (le_of_lt hCZ) hw1le
      rw [← hcross] at hrhs
      exact (not_lt_of_ge hrhs) (mul_pos hEZ hw2)
  · constructor
    · intro hw1
      by_contra hn
      have hw2ge : 0 ≤ w2 := le_of_not_gt hn
      have hlhs : 0 ≤ (E : ℤ) * w2 :=
        mul_nonneg (le_of_lt hEZ) hw2ge
      rw [hcross] at hlhs
      exact (not_lt_of_ge hlhs) (mul_neg_of_pos_of_neg hCZ hw1)
    · intro hw2
      by_contra hn
      have hw1ge : 0 ≤ w1 := le_of_not_gt hn
      have hrhs : 0 ≤ (C : ℤ) * w1 :=
        mul_nonneg (le_of_lt hCZ) hw1ge
      rw [← hcross] at hrhs
      exact (not_lt_of_ge hrhs) (mul_neg_of_pos_of_neg hEZ hw2)

/-- Over a characteristic-zero field, the first sparse pencil cannot vanish
identically when `C,E,F` are positive natural exponents.  Evaluation at
`t=1` already detects a nonzero determinant. -/
theorem sparseRankThreePencil_det_one_ne_zero
    {K : Type*} [Field K] [CharZero K]
    {C D E F : ℕ} (hC : 0 < C) (hE : 0 < E) (hF : 0 < F) :
    (sparseRankThreePencil (K := K) C D E F 1).det ≠ 0 := by
  rw [det_sparseRankThreePencil]
  simp only [one_pow, mul_one]
  have hCE : 0 < C + E - 1 := by omega
  have hC0 : (C : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hC)
  have hE0 : (E : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hE)
  have hF0 : (F : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hF)
  have hCE0 : ((C + E - 1 : ℕ) : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hCE)
  have hNat : C + E = (C + E - 1) + 1 := by omega
  have hCast : (C : K) + (E : K) = ((C + E - 1 : ℕ) : K) + 1 := by
    exact_mod_cast hNat
  have hFactor : (C : K) + (E : K) - 1 = ((C + E - 1 : ℕ) : K) :=
    (sub_eq_iff_eq_add).2 hCast
  rw [hFactor]
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero hC0 hE0) (pow_ne_zero 2 hF0)) hCE0

end

end HC4.Polynomial
