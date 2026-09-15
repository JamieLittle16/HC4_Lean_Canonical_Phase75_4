import HC4.Polynomial.RankThreePencils
import Mathlib.Tactic

/-!
# Nonhomogeneous codimension-two departure pencil

The finite-staircase central roof transition is not ordinarily homogeneous, so
the homogeneous `CodimensionTwoPrimitiveDeparturePencil` cannot be applied
literally.  The first mixed Hessian coefficient does not need homogeneity.

For exponent vectors

    v = (p, 0, 0, r),
    u = (a, 0, m, b),
    w = (c, n, 0, d),

and honest source coefficients `C,A,B`, consider

    C M(v) + s A M(u) + t B M(w),

where `M(e) = e e^T - diag(e)`.  The coefficient of `s*t` in the determinant
is

    -C^2 A B m n p r (p+r-1) (m-1) (n-1).

In the central finite-staircase application `m` and `n` are the two roof
residuals.  Thus two genuinely nonprimitive departures (`m,n >= 2`) cannot
occur around a positive codimension-two base monomial in a singular carrier.

This file is completely state-free.
-/

namespace HC4.Polynomial

open scoped Matrix

noncomputable section

private def nestedCnh {K : Type*} [CommRing K]
    (x : K) : Polynomial (Polynomial K) :=
  Polynomial.C (Polynomial.C x)

private def sVarnh {K : Type*} [CommRing K] :
    Polynomial (Polynomial K) := Polynomial.X

private def tVarnh {K : Type*} [CommRing K] :
    Polynomial (Polynomial K) := Polynomial.C Polynomial.X

/-- Coefficient-weighted two-parameter Hessian core around a possibly
nonhomogeneous codimension-two base monomial.  The `s` departure opens
coordinate `2`, while the `t` departure opens coordinate `1`. -/
noncomputable def codimensionTwoNonhomogeneousDeparturePencil
    {K : Type*} [CommRing K]
    (p r a m b c n d C A B : K) :
    Matrix (Fin 4) (Fin 4) (Polynomial (Polynomial K)) :=
  Matrix.of fun i j =>
    nestedCnh C * nestedCnh
        (vectorHessianCore (K := K) ![p, 0, 0, r] i j) +
      sVarnh * nestedCnh A * nestedCnh
        (vectorHessianCore (K := K) ![a, 0, m, b] i j) +
      tVarnh * nestedCnh B * nestedCnh
        (vectorHessianCore (K := K) ![c, n, 0, d] i j)

set_option maxHeartbeats 5000000 in
/-- **First mixed nonhomogeneous codimension-two coefficient.**

The longitudinal coordinates `a,b,c,d` cancel completely from the first mixed
coefficient.  Only the positive base coordinates and the two missing-coordinate
departure sizes remain. -/
theorem coeff_s_t_det_codimensionTwoNonhomogeneousDeparturePencil
    {K : Type*} [CommRing K]
    (p r a m b c n d C A B : K) :
    (((codimensionTwoNonhomogeneousDeparturePencil
      p r a m b c n d C A B).det).coeff 1).coeff 1 =
      -(C ^ 2 * A * B *
        (m * n * p * r * (p + r - 1) * (m - 1) * (n - 1))) := by
  rw [Matrix.det_succ_row_zero]
  simp only [Fin.sum_univ_four]
  simp [codimensionTwoNonhomogeneousDeparturePencil,
    nestedCnh, sVarnh, tVarnh, vectorHessianCore,
    Matrix.det_fin_three, Fin.succAbove]
  ring

/-- If the full two-parameter core is singular and the base/source factors are
nonzero, at least one of the two transverse departures is primitive. -/
theorem singular_codimensionTwoNonhomogeneousDeparturePencil_forces_primitive
    {K : Type*} [Field K] [CharZero K]
    {p r a m b c n d : ℕ} {C A B : K}
    (hp : 0 < p) (hr : 0 < r)
    (hm : 0 < m) (hn : 0 < n)
    (hC : C ≠ 0) (hA : A ≠ 0) (hB : B ≠ 0)
    (hsing :
      (codimensionTwoNonhomogeneousDeparturePencil
        (p : K) (r : K) (a : K) (m : K) (b : K)
        (c : K) (n : K) (d : K) C A B).det = 0) :
    m = 1 ∨ n = 1 := by
  have hcoeff :
      -(C ^ 2 * A * B *
        ((m : K) * (n : K) * (p : K) * (r : K) *
          ((p : K) + (r : K) - 1) * ((m : K) - 1) * ((n : K) - 1))) = 0 := by
    calc
      _ = (((codimensionTwoNonhomogeneousDeparturePencil
          (p : K) (r : K) (a : K) (m : K) (b : K)
          (c : K) (n : K) (d : K) C A B).det).coeff 1).coeff 1 := by
            symm
            exact coeff_s_t_det_codimensionTwoNonhomogeneousDeparturePencil
              (K := K) (p : K) (r : K) (a : K) (m : K) (b : K)
              (c : K) (n : K) (d : K) C A B
      _ = 0 := by rw [hsing]; simp
  have hpK : (p : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hp)
  have hrK : (r : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hr)
  have hmK : (m : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hm)
  have hnK : (n : K) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hn)
  have hpr1Nat : 0 < p + r - 1 := by omega
  have hpr1K : (p : K) + (r : K) - 1 ≠ 0 := by
    have hcast : (((p + r - 1 : ℕ) : K)) ≠ 0 := by
      exact_mod_cast (Nat.ne_of_gt hpr1Nat)
    have hle : 1 ≤ p + r := by omega
    rw [Nat.cast_sub hle, Nat.cast_add] at hcast
    norm_num at hcast ⊢
    exact hcast
  have hknown :
      C ^ 2 * A * B * (m : K) * (n : K) * (p : K) * (r : K) *
          ((p : K) + (r : K) - 1) ≠ 0 := by
    repeat' apply mul_ne_zero
    · exact pow_ne_zero 2 hC
    · exact hA
    · exact hB
    · exact hmK
    · exact hnK
    · exact hpK
    · exact hrK
    · exact hpr1K
  have hmn : ((m : K) - 1) * ((n : K) - 1) = 0 := by
    have hz := neg_eq_zero.mp hcoeff
    have hz' :
        (C ^ 2 * A * B * (m : K) * (n : K) * (p : K) * (r : K) *
            ((p : K) + (r : K) - 1)) *
          (((m : K) - 1) * ((n : K) - 1)) = 0 := by
      simpa [mul_assoc] using hz
    exact (mul_eq_zero.mp hz').resolve_left hknown
  rcases mul_eq_zero.mp hmn with hm1K | hn1K
  · left
    have hmcast : (m : K) = 1 := sub_eq_zero.mp hm1K
    exact_mod_cast hmcast
  · right
    have hncast : (n : K) = 1 := sub_eq_zero.mp hn1K
    exact_mod_cast hncast

end

end HC4.Polynomial