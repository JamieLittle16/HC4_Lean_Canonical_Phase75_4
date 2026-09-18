import HC4.Polynomial.CodimensionTwoNonhomogeneousDeparturePencil
import Mathlib.Tactic

/-!
# Nonhomogeneous codimension-two joint-departure obstruction

The finite-staircase central branch has a positive codimension-two base
monomial

    v = (p, 0, 0, r)

and may a priori contain a supported monomial which opens both missing
coordinates,

    u = (a, m, n, b),    m,n > 0.

For the coefficient-weighted Hessian core pencil

    C M(v) + X A M(u),

the determinant coefficient at order two is

    A^2 C^2 m n p r (m+n-1) (p+r-1).

Every factor is nonzero over a characteristic-zero field when the two base
coordinates, the two joint departure coordinates, and the honest source
coefficients are nonzero.  Hence such a two-term pencil cannot be singular.

This is the state-free joint-departure companion to
`CodimensionTwoNonhomogeneousDeparturePencil`.  It introduces no valuation
clock and no repair state.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

/-- Coefficient-weighted one-parameter Hessian core of a positive
codimension-two base monomial and one joint departure. -/
noncomputable def codimensionTwoNonhomogeneousJointPencil
    {K : Type*} [CommRing K]
    (p r a m n b C A : K) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  Matrix.of fun i j =>
    Polynomial.C C *
        Polynomial.C
          (vectorHessianCore (K := K) ![p, 0, 0, r] i j) +
      Polynomial.X * Polynomial.C A *
        Polynomial.C
          (vectorHessianCore (K := K) ![a, m, n, b] i j)

set_option maxHeartbeats 5000000 in
/-- **Exact joint-departure second determinant coefficient.** -/
theorem coeff_two_det_codimensionTwoNonhomogeneousJointPencil
    {K : Type*} [CommRing K]
    (p r a m n b C A : K) :
    (codimensionTwoNonhomogeneousJointPencil
        p r a m n b C A).det.coeff 2 =
      A ^ 2 * C ^ 2 * m * n * p * r *
        (m + n - 1) * (p + r - 1) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [codimensionTwoNonhomogeneousJointPencil,
    vectorHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- A genuine joint departure from a positive codimension-two base cannot
occur in an identically singular two-term Hessian core pencil. -/
theorem codimensionTwoNonhomogeneousJointPencil_not_singular
    {K : Type*} [Field K] [CharZero K]
    {p r a m n b : ℕ} {C A : K}
    (hp : 0 < p) (hr : 0 < r)
    (hm : 0 < m) (hn : 0 < n)
    (hC : C ≠ 0) (hA : A ≠ 0)
    (hsing :
      (codimensionTwoNonhomogeneousJointPencil
        (p : K) (r : K) (a : K) (m : K) (n : K) (b : K) C A).det = 0) :
    False := by
  have hcoeff :
      A ^ 2 * C ^ 2 * (m : K) * (n : K) * (p : K) * (r : K) *
          ((m : K) + (n : K) - 1) *
          ((p : K) + (r : K) - 1) = 0 := by
    calc
      _ =
          (codimensionTwoNonhomogeneousJointPencil
            (p : K) (r : K) (a : K) (m : K) (n : K) (b : K) C A).det.coeff 2 := by
              symm
              exact coeff_two_det_codimensionTwoNonhomogeneousJointPencil
                (K := K) (p : K) (r : K) (a : K)
                (m : K) (n : K) (b : K) C A
      _ = 0 := by rw [hsing]; simp
  have hpK : (p : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hrK : (r : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hmK : (m : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hnK : (n : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hmnNat : 0 < m + n - 1 := by omega
  have hprNat : 0 < p + r - 1 := by omega
  have hmnK : (m : K) + (n : K) - 1 ≠ 0 := by
    have hcast : (((m + n - 1 : ℕ) : K)) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hmnNat)
    rw [Nat.cast_sub (by omega : 1 ≤ m + n), Nat.cast_add] at hcast
    norm_num at hcast ⊢
    exact hcast
  have hprK : (p : K) + (r : K) - 1 ≠ 0 := by
    have hcast : (((p + r - 1 : ℕ) : K)) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hprNat)
    rw [Nat.cast_sub (by omega : 1 ≤ p + r), Nat.cast_add] at hcast
    norm_num at hcast ⊢
    exact hcast
  have hne :
      A ^ 2 * C ^ 2 * (m : K) * (n : K) * (p : K) * (r : K) *
          ((m : K) + (n : K) - 1) *
          ((p : K) + (r : K) - 1) ≠ 0 := by
    repeat' apply mul_ne_zero
    · exact pow_ne_zero 2 hA
    · exact pow_ne_zero 2 hC
    · exact hmK
    · exact hnK
    · exact hpK
    · exact hrK
    · exact hmnK
    · exact hprK
  exact hne hcoeff

end

end HC4.Polynomial
