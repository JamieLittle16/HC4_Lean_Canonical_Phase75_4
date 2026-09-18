import HC4.Polynomial.CodimensionTwoNonhomogeneousJointDeparture
import Mathlib.Tactic

/-!
# Nonhomogeneous codimension-two separated-departure obstruction

For the central finite-staircase base monomial

    v = (p,0,0,r)

and two separated roof departures

    u = (a,0,m,b),    w = (c,n,0,d),

the one-parameter first layer is the coefficient-weighted sum of their Hessian
cores.  The order-two determinant coefficient of

    C M(v) + X (A M(u) + B M(w))

is

    - A B C^2 m n p r (m-1)(n-1)(p+r-1).

Thus, over a characteristic-zero field, an identically singular pencil with
positive honest coefficients/exponents forces at least one departure to be
primitive.  In the central finite-staircase application both roof residuals
are at least two, so this coefficient gives the desired contradiction once the
source-honest first-layer adapter is supplied.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

/-- One-parameter Hessian core with two separated first-order departures. -/
noncomputable def codimensionTwoNonhomogeneousSeparatedPencil
    {K : Type*} [CommRing K]
    (p r a m b c n d C A B : K) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  Matrix.of fun i j =>
    Polynomial.C C *
        Polynomial.C
          (vectorHessianCore (K := K) ![p, 0, 0, r] i j) +
      Polynomial.X *
        (Polynomial.C A *
            Polynomial.C
              (vectorHessianCore (K := K) ![a, 0, m, b] i j) +
          Polynomial.C B *
            Polynomial.C
              (vectorHessianCore (K := K) ![c, n, 0, d] i j))

set_option maxHeartbeats 5000000 in
/-- **Exact separated-departure second determinant coefficient.** -/
theorem coeff_two_det_codimensionTwoNonhomogeneousSeparatedPencil
    {K : Type*} [CommRing K]
    (p r a m b c n d C A B : K) :
    (codimensionTwoNonhomogeneousSeparatedPencil
        p r a m b c n d C A B).det.coeff 2 =
      -(A * B * C ^ 2 * m * n * p * r *
        (m - 1) * (n - 1) * (p + r - 1)) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [codimensionTwoNonhomogeneousSeparatedPencil,
    vectorHessianCore, Matrix.det_fin_three, Fin.succAbove]
  ring

/-- If both separated departures are nonprimitive, the one-parameter
central/departure pencil cannot be identically singular. -/
theorem codimensionTwoNonhomogeneousSeparatedPencil_not_singular
    {K : Type*} [Field K] [CharZero K]
    {p r a m b c n d : ℕ} {C A B : K}
    (hp : 0 < p) (hr : 0 < r)
    (hm : 1 < m) (hn : 1 < n)
    (hC : C ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hsing :
      (codimensionTwoNonhomogeneousSeparatedPencil
        (p : K) (r : K)
        (a : K) (m : K) (b : K)
        (c : K) (n : K) (d : K)
        C A B).det = 0) :
    False := by
  have hcoeff :
      -(A * B * C ^ 2 * (m : K) * (n : K) * (p : K) * (r : K) *
        ((m : K) - 1) * ((n : K) - 1) *
        ((p : K) + (r : K) - 1)) = 0 := by
    calc
      _ =
          (codimensionTwoNonhomogeneousSeparatedPencil
            (p : K) (r : K)
            (a : K) (m : K) (b : K)
            (c : K) (n : K) (d : K)
            C A B).det.coeff 2 := by
              symm
              exact coeff_two_det_codimensionTwoNonhomogeneousSeparatedPencil
                (K := K)
                (p : K) (r : K)
                (a : K) (m : K) (b : K)
                (c : K) (n : K) (d : K)
                C A B
      _ = 0 := by rw [hsing]; simp
  have hpK : (p : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hrK : (r : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hmK : (m : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < m))
  have hnK : (n : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt (by omega : 0 < n))
  have hm1K : (m : K) - 1 ≠ 0 := by
    intro hz
    have hcast : (m : K) = 1 := sub_eq_zero.mp hz
    have hnat : m = 1 := by exact_mod_cast hcast
    omega
  have hn1K : (n : K) - 1 ≠ 0 := by
    intro hz
    have hcast : (n : K) = 1 := sub_eq_zero.mp hz
    have hnat : n = 1 := by exact_mod_cast hcast
    omega
  have hprNat : 0 < p + r - 1 := by omega
  have hprK : (p : K) + (r : K) - 1 ≠ 0 := by
    have hcast : (((p + r - 1 : ℕ) : K)) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hprNat)
    rw [Nat.cast_sub (by omega : 1 ≤ p + r), Nat.cast_add] at hcast
    norm_num at hcast ⊢
    exact hcast
  have hne :
      A * B * C ^ 2 * (m : K) * (n : K) * (p : K) * (r : K) *
        ((m : K) - 1) * ((n : K) - 1) *
        ((p : K) + (r : K) - 1) ≠ 0 := by
    repeat' apply mul_ne_zero
    · exact hA
    · exact hB
    · exact pow_ne_zero 2 hC
    · exact hmK
    · exact hnK
    · exact hpK
    · exact hrK
    · exact hm1K
    · exact hn1K
    · exact hprK
  exact hne (neg_eq_zero.mp hcoeff)

end

end HC4.Polynomial
