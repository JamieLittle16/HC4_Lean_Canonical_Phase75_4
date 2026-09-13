import HC4.Polynomial.TwoFunctionEulerHessian
import Mathlib.Tactic

/-!
# Two-function carrier coefficient rigidity

This file isolates the small polynomial-algebra contradiction after the second
Euler-Hessian factor has been shown to vanish.  The four hypotheses below are
exactly the `x H^0`, `x H^ell`, `z H^0`, and `z H^ell` coefficient equations
of `twoFunctionEulerFactorB = 0`.

They force `ell = 1` and `Q'' = 0`.  Differentiating the `z H^0` equation then
gives `b P'' = a Q'`, while the `z H^ell` equation gives
`b P'' = 4 a Q'`, contradicting characteristic zero when `a,b,Q'` are
nonzero.
-/

namespace HC4.Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- **Coefficient-level no-two-function theorem.** -/
theorem twoFunction_factorB_coefficients_impossible
    (ell : ℕ) (hell : 0 < ell)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (P Q : Polynomial K)
    (hQ1 : Q.derivative ≠ 0)
    (hX0 :
      Polynomial.C b * Polynomial.C ((ell : K) - 1) * Q.derivative ^ 2 = 0)
    (hXell :
      Polynomial.C b ^ 2 * Polynomial.C (ell : K) *
          Q.derivative.derivative = 0)
    (hZ0 :
      Polynomial.C a * Polynomial.C ((ell : K) + 1) * Polynomial.X *
          Q.derivative ^ 2 -
        Polynomial.C 2 * Polynomial.C b * P.derivative * Q.derivative = 0)
    (hZell :
      -(Polynomial.C 2 * Polynomial.C a * Polynomial.C b *
          Polynomial.C ((ell : K) + 1) * Q.derivative) +
        Polynomial.C b ^ 2 * Polynomial.C (ell : K) *
          P.derivative.derivative = 0) :
    False := by
  have hbC : Polynomial.C b ≠ (0 : Polynomial K) :=
    Polynomial.C_ne_zero.mpr hb
  have hQsq : Q.derivative ^ 2 ≠ (0 : Polynomial K) :=
    pow_ne_zero _ hQ1
  have hellSubC : Polynomial.C ((ell : K) - 1) = (0 : Polynomial K) := by
    have hleft :
        Polynomial.C b * Polynomial.C ((ell : K) - 1) = 0 :=
      (mul_eq_zero.mp hX0).resolve_right hQsq
    exact (mul_eq_zero.mp hleft).resolve_left hbC
  have hellSub : (ell : K) - 1 = 0 := by
    exact Polynomial.C_injective hellSubC
  have hellCast : (ell : K) = 1 := sub_eq_zero.mp hellSub
  have hellOne : ell = 1 := by exact_mod_cast hellCast

  have hellK : (ell : K) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hell)
  have hellC : Polynomial.C (ell : K) ≠ (0 : Polynomial K) :=
    Polynomial.C_ne_zero.mpr hellK
  have hbSqC : Polynomial.C b ^ 2 ≠ (0 : Polynomial K) :=
    pow_ne_zero _ hbC
  have hQ2 : Q.derivative.derivative = 0 := by
    have hpref : Polynomial.C b ^ 2 * Polynomial.C (ell : K) ≠
        (0 : Polynomial K) := mul_ne_zero hbSqC hellC
    exact (mul_eq_zero.mp hXell).resolve_left hpref

  subst ell
  norm_num at hZ0 hZell

  have hZ0d := congrArg Polynomial.derivative hZ0
  simp only [Polynomial.derivative_sub, Polynomial.derivative_mul,
    Polynomial.derivative_C, Polynomial.derivative_X, hQ2,
    zero_mul, mul_zero, add_zero, zero_add] at hZ0d
  ring_nf at hZ0d

  have hfact1 :
      (Polynomial.C (2 : K) * Q.derivative) *
        (Polynomial.C a * Q.derivative -
          Polynomial.C b * P.derivative.derivative) = 0 := by
    linear_combination hZ0d
  have htwoK : (2 : K) ≠ 0 := by norm_num
  have htwoC : Polynomial.C (2 : K) ≠ (0 : Polynomial K) :=
    Polynomial.C_ne_zero.mpr htwoK
  have htwoQ : Polynomial.C (2 : K) * Q.derivative ≠
      (0 : Polynomial K) := mul_ne_zero htwoC hQ1
  have hrel1zero :
      Polynomial.C a * Q.derivative -
        Polynomial.C b * P.derivative.derivative = 0 :=
    (mul_eq_zero.mp hfact1).resolve_left htwoQ
  have hrel1 :
      Polynomial.C b * P.derivative.derivative =
        Polynomial.C a * Q.derivative := by
    exact (sub_eq_zero.mp hrel1zero).symm

  have hfact4 :
      Polynomial.C b *
        (Polynomial.C b * P.derivative.derivative -
          Polynomial.C 4 * Polynomial.C a * Q.derivative) = 0 := by
    linear_combination hZell
  have hrel4zero :
      Polynomial.C b * P.derivative.derivative -
        Polynomial.C 4 * Polynomial.C a * Q.derivative = 0 :=
    (mul_eq_zero.mp hfact4).resolve_left hbC
  have hrel4 :
      Polynomial.C b * P.derivative.derivative =
        Polynomial.C 4 * Polynomial.C a * Q.derivative :=
    sub_eq_zero.mp hrel4zero

  have hthree :
      Polynomial.C (3 : K) * Polynomial.C a * Q.derivative = 0 := by
    linear_combination hrel4 - hrel1
  have hthreeK : (3 : K) ≠ 0 := by norm_num
  have hthreeC : Polynomial.C (3 : K) ≠ (0 : Polynomial K) :=
    Polynomial.C_ne_zero.mpr hthreeK
  have haC : Polynomial.C a ≠ (0 : Polynomial K) :=
    Polynomial.C_ne_zero.mpr ha
  have hnonzero :
      Polynomial.C (3 : K) * Polynomial.C a * Q.derivative ≠
        (0 : Polynomial K) :=
    mul_ne_zero (mul_ne_zero hthreeC haC) hQ1
  exact hnonzero hthree

end

end HC4.Polynomial
