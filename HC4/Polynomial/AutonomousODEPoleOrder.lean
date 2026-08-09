import HC4.Polynomial.AutonomousODEQuadraticRigidity
import Mathlib.Tactic

/-!
# Local pole order for autonomous logarithmic ODEs

This file replaces the manuscript's Laurent expansion at a nonzero root by
exact polynomial coefficient identities.

After translating a nonzero root `alpha` to the origin, ordinary Euler
multiplication by `t` becomes multiplication by `X + alpha`.  We therefore
write

    E_alpha(p) = (X + alpha) p'.

If

    phi = X^(n+1) q,   q(0) != 0,

then the original root has multiplicity `n+1`.  We prove exactly that

    E_alpha(phi)

has first nonzero coefficient in degree `n`, equal to

    alpha * (n+1) * q(0),

and that the cleared numerator of `(X+alpha) d/dX (E_alpha(phi)/phi)`
has first nonzero coefficient in degree `2n`, equal to

    -alpha^2 * (n+1) * q(0)^2.

These are the coefficient-theoretic forms of

    rho ~ M alpha / X,
    t rho' ~ -(1/M) rho^2.

They are the local input needed to force an autonomous polynomial right-hand
side to have degree exactly two.
-/

namespace HC4.Polynomial

noncomputable section

/-- Euler differentiation after translating the original point `alpha` to
`X = 0`: the original coordinate is `X + alpha`. -/
def shiftedEuler
    {K : Type*} [CommRing K]
    (alpha : K) (p : Polynomial K) : Polynomial K :=
  (Polynomial.X + Polynomial.C alpha) * Polynomial.derivative p

/-- Cleared numerator of the shifted logarithmic second derivative. -/
def shiftedEtaNumerator
    {K : Type*} [CommRing K]
    (alpha : K) (p : Polynomial K) : Polynomial K :=
  shiftedEuler alpha (shiftedEuler alpha p) * p -
    (shiftedEuler alpha p)^2

/-- The coefficient-bearing factor in the shifted Euler derivative of
`X^M q`. -/
def shiftedEulerCore
    {K : Type*} [CommRing K]
    (alpha : K) (M : ℕ) (q : Polynomial K) : Polynomial K :=
  (Polynomial.X + Polynomial.C alpha) *
    (Polynomial.C (M : K) * q + Polynomial.X * Polynomial.derivative q)

/-- Multiplication of two polynomials with explicit `X`-power factors. -/
theorem X_pow_mul_mul_X_pow_mul
    {K : Type*} [CommRing K]
    (a b : ℕ) (p q : Polynomial K) :
    (Polynomial.X ^ a * p) * (Polynomial.X ^ b * q) =
      Polynomial.X ^ (a + b) * (p * q) := by
  calc
    (Polynomial.X ^ a * p) * (Polynomial.X ^ b * q) =
        (Polynomial.X ^ a * Polynomial.X ^ b) * (p * q) := by ring
    _ = Polynomial.X ^ (a + b) * (p * q) := by rw [pow_add]

/-- Exact shifted-Euler factorisation at a root of multiplicity `n+1`. -/
theorem shiftedEuler_X_pow_succ_mul
    {K : Type*} [CommRing K]
    (alpha : K) (q : Polynomial K) (n : ℕ) :
    shiftedEuler alpha (Polynomial.X ^ (n + 1) * q) =
      Polynomial.X ^ n * shiftedEulerCore alpha (n + 1) q := by
  unfold shiftedEuler shiftedEulerCore
  rw [Polynomial.derivative_mul, Polynomial.derivative_X_pow_succ]
  push_cast
  ring

/-- Constant coefficient of the shifted-Euler core. -/
theorem coeff_zero_shiftedEulerCore
    {K : Type*} [CommRing K]
    (alpha : K) (M : ℕ) (q : Polynomial K) :
    (shiftedEulerCore alpha M q).coeff 0 =
      alpha * (M : K) * q.coeff 0 := by
  simp [shiftedEulerCore, Polynomial.mul_coeff_zero] <;> ring

/-- The first coefficient of the shifted logarithmic numerator `rho` at a
root of multiplicity `n+1`. -/
theorem coeff_n_shiftedEuler_X_pow_succ_mul
    {K : Type*} [CommRing K]
    (alpha : K) (q : Polynomial K) (n : ℕ) :
    (shiftedEuler alpha (Polynomial.X ^ (n + 1) * q)).coeff n =
      alpha * ((n + 1 : ℕ) : K) * q.coeff 0 := by
  rw [shiftedEuler_X_pow_succ_mul]
  rw [Polynomial.coeff_X_pow_mul']
  simp [coeff_zero_shiftedEulerCore]

/-- Exact first coefficient of the shifted cleared `eta` numerator.

For multiplicity `M = n+1`, its order is `2M-2 = 2n`, and the coefficient
is `-alpha^2 * M * q(0)^2`. -/
theorem coeff_two_n_shiftedEtaNumerator_X_pow_succ_mul
    {K : Type*} [CommRing K]
    (alpha : K) (q : Polynomial K) (n : ℕ) :
    (shiftedEtaNumerator alpha
      (Polynomial.X ^ (n + 1) * q)).coeff (n + n) =
      -(alpha^2 * ((n + 1 : ℕ) : K) * (q.coeff 0)^2) := by
  cases n with
  | zero =>
      have hE := shiftedEuler_X_pow_succ_mul
        (K := K) alpha q 0
      unfold shiftedEtaNumerator
      rw [hE]
      simp only [zero_add, pow_zero, one_mul]
      rw [Polynomial.coeff_sub]
      simp [Polynomial.mul_coeff_zero, coeff_zero_shiftedEulerCore,
        pow_two] <;> ring
  | succ k =>
      let g : Polynomial K := shiftedEulerCore alpha (k + 2) q
      let h : Polynomial K := shiftedEulerCore alpha (k + 1) g
      have hE :
          shiftedEuler alpha (Polynomial.X ^ (k + 2) * q) =
            Polynomial.X ^ (k + 1) * g := by
        simpa [g, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using
          shiftedEuler_X_pow_succ_mul (K := K) alpha q (k + 1)
      have hEE :
          shiftedEuler alpha (Polynomial.X ^ (k + 1) * g) =
            Polynomial.X ^ k * h := by
        simpa [h] using
          shiftedEuler_X_pow_succ_mul (K := K) alpha g k
      have hsum₁ : k + (k + 2) = (k + 1) + (k + 1) := by omega
      have hfactor :
          (Polynomial.X ^ k * h) * (Polynomial.X ^ (k + 2) * q) -
              (Polynomial.X ^ (k + 1) * g)^2 =
            Polynomial.X ^ ((k + 1) + (k + 1)) * (h * q - g^2) := by
        rw [X_pow_mul_mul_X_pow_mul]
        rw [hsum₁]
        rw [pow_two, X_pow_mul_mul_X_pow_mul]
        ring
      unfold shiftedEtaNumerator
      rw [hE, hEE, hfactor]
      rw [Polynomial.coeff_X_pow_mul']
      simp only [le_refl, if_true, Nat.sub_self]
      rw [Polynomial.coeff_sub, Polynomial.mul_coeff_zero]
      rw [show (g^2).coeff 0 = (g.coeff 0)^2 by
        simp [pow_two, Polynomial.mul_coeff_zero]]
      rw [coeff_zero_shiftedEulerCore]
      change
        alpha * ((k + 1 : ℕ) : K) * g.coeff 0 * q.coeff 0 -
            (g.coeff 0)^2 =
          -(alpha ^ 2 * ((k + 2 : ℕ) : K) * (q.coeff 0)^2)
      rw [show g.coeff 0 =
          alpha * ((k + 2 : ℕ) : K) * q.coeff 0 by
        dsimp [g]
        exact coeff_zero_shiftedEulerCore alpha (k + 2) q]
      push_cast
      ring

/-- At a genuine nonzero root, the first shifted-Euler coefficient is
nonzero. -/
theorem coeff_n_shiftedEuler_ne_zero
    {K : Type*} [Field K] [CharZero K]
    {alpha : K} {q : Polynomial K} {n : ℕ}
    (halpha : alpha ≠ 0) (hq0 : q.coeff 0 ≠ 0) :
    (shiftedEuler alpha (Polynomial.X ^ (n + 1) * q)).coeff n ≠ 0 := by
  rw [coeff_n_shiftedEuler_X_pow_succ_mul]
  have hM : (((n + 1 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  exact mul_ne_zero (mul_ne_zero halpha hM) hq0

/-- At a genuine nonzero root, the first shifted `eta` numerator coefficient
is nonzero as well. -/
theorem coeff_two_n_shiftedEtaNumerator_ne_zero
    {K : Type*} [Field K] [CharZero K]
    {alpha : K} {q : Polynomial K} {n : ℕ}
    (halpha : alpha ≠ 0) (hq0 : q.coeff 0 ≠ 0) :
    (shiftedEtaNumerator alpha
      (Polynomial.X ^ (n + 1) * q)).coeff (n + n) ≠ 0 := by
  rw [coeff_two_n_shiftedEtaNumerator_X_pow_succ_mul]
  have hM : (((n + 1 : ℕ) : K)) ≠ 0 := by
    exact_mod_cast (Nat.succ_ne_zero n)
  have ha2 : alpha^2 ≠ 0 := pow_ne_zero 2 halpha
  have hq2 : (q.coeff 0)^2 ≠ 0 := pow_ne_zero 2 hq0
  exact neg_ne_zero.mpr (mul_ne_zero (mul_ne_zero ha2 hM) hq2)

end

end HC4.Polynomial
