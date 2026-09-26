import HC4.Polynomial.TwoFunctionEulerRigidity
import Mathlib.Tactic

/-!
# H-series form of the two-function Euler factor

The second Euler-Hessian factor is linear in the independent source variables
`x,z`.  Its two coefficients are sparse polynomials in `H`, with coefficient
ring `K[Y]`.  Encoding those coefficients with `Polynomial.monomial` makes the
four paper coefficient equations literal coefficient extractions at indices
`0` and `ell`.
-/

namespace HC4.Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Coefficient of `x` in the second Euler-Hessian factor, viewed as a
polynomial in `H` over `K[Y]`. -/
def twoFunctionFactorBxSeries
    (ell : ℕ) (b : K) (Q : Polynomial K) :
    Polynomial (Polynomial K) :=
  Polynomial.C
      (Polynomial.C b * Polynomial.C ((ell : K) - 1) * Q.derivative ^ 2) +
    Polynomial.monomial ell
      (Polynomial.C b ^ 2 * Polynomial.C (ell : K) *
        Q.derivative.derivative)

/-- Coefficient of `z` in the second Euler-Hessian factor, viewed as a
polynomial in `H` over `K[Y]`. -/
def twoFunctionFactorBzSeries
    (ell : ℕ) (a b : K) (P Q : Polynomial K) :
    Polynomial (Polynomial K) :=
  Polynomial.C
      (Polynomial.C a * Polynomial.C ((ell : K) + 1) * Polynomial.X *
          Q.derivative ^ 2 -
        Polynomial.C 2 * Polynomial.C b * P.derivative * Q.derivative) +
    Polynomial.monomial ell
      (-(Polynomial.C 2 * Polynomial.C a * Polynomial.C b *
          Polynomial.C ((ell : K) + 1) * Q.derivative) +
        Polynomial.C b ^ 2 * Polynomial.C (ell : K) *
          P.derivative.derivative)

/-- The constant `H` coefficient of `Bx`. -/
theorem coeff_zero_twoFunctionFactorBxSeries
    (ell : ℕ) (hell : 0 < ell) (b : K) (Q : Polynomial K) :
    (twoFunctionFactorBxSeries ell b Q).coeff 0 =
      Polynomial.C b * Polynomial.C ((ell : K) - 1) * Q.derivative ^ 2 := by
  have hell0 : ell ≠ 0 := Nat.ne_of_gt hell
  simp [twoFunctionFactorBxSeries, Polynomial.coeff_monomial, hell0]

/-- The top `H^ell` coefficient of `Bx`. -/
theorem coeff_ell_twoFunctionFactorBxSeries
    (ell : ℕ) (hell : 0 < ell) (b : K) (Q : Polynomial K) :
    (twoFunctionFactorBxSeries ell b Q).coeff ell =
      Polynomial.C b ^ 2 * Polynomial.C (ell : K) *
        Q.derivative.derivative := by
  have hell0 : ell ≠ 0 := Nat.ne_of_gt hell
  simp [twoFunctionFactorBxSeries, Polynomial.coeff_monomial, hell0,
    Ne.symm hell0]

/-- The constant `H` coefficient of `Bz`. -/
theorem coeff_zero_twoFunctionFactorBzSeries
    (ell : ℕ) (hell : 0 < ell) (a b : K) (P Q : Polynomial K) :
    (twoFunctionFactorBzSeries ell a b P Q).coeff 0 =
      Polynomial.C a * Polynomial.C ((ell : K) + 1) * Polynomial.X *
          Q.derivative ^ 2 -
        Polynomial.C 2 * Polynomial.C b * P.derivative * Q.derivative := by
  have hell0 : ell ≠ 0 := Nat.ne_of_gt hell
  simp [twoFunctionFactorBzSeries, Polynomial.coeff_monomial, hell0]

/-- The top `H^ell` coefficient of `Bz`. -/
theorem coeff_ell_twoFunctionFactorBzSeries
    (ell : ℕ) (hell : 0 < ell) (a b : K) (P Q : Polynomial K) :
    (twoFunctionFactorBzSeries ell a b P Q).coeff ell =
      -(Polynomial.C 2 * Polynomial.C a * Polynomial.C b *
          Polynomial.C ((ell : K) + 1) * Q.derivative) +
        Polynomial.C b ^ 2 * Polynomial.C (ell : K) *
          P.derivative.derivative := by
  have hell0 : ell ≠ 0 := Nat.ne_of_gt hell
  simp [twoFunctionFactorBzSeries, Polynomial.coeff_monomial, hell0,
    Ne.symm hell0]

/-- **The sparse `H`-series second factor cannot vanish.** -/
theorem twoFunction_factorB_series_impossible
    (ell : ℕ) (hell : 0 < ell)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (P Q : Polynomial K) (hQ1 : Q.derivative ≠ 0)
    (hBx : twoFunctionFactorBxSeries ell b Q = 0)
    (hBz : twoFunctionFactorBzSeries ell a b P Q = 0) :
    False := by
  have hX0 :
      Polynomial.C b * Polynomial.C ((ell : K) - 1) * Q.derivative ^ 2 = 0 := by
    have h := congrArg (fun f : Polynomial (Polynomial K) => f.coeff 0) hBx
    rw [coeff_zero_twoFunctionFactorBxSeries ell hell] at h
    simpa using h
  have hXell :
      Polynomial.C b ^ 2 * Polynomial.C (ell : K) *
          Q.derivative.derivative = 0 := by
    have h := congrArg (fun f : Polynomial (Polynomial K) => f.coeff ell) hBx
    rw [coeff_ell_twoFunctionFactorBxSeries ell hell] at h
    simpa using h
  have hZ0 :
      Polynomial.C a * Polynomial.C ((ell : K) + 1) * Polynomial.X *
          Q.derivative ^ 2 -
        Polynomial.C 2 * Polynomial.C b * P.derivative * Q.derivative = 0 := by
    have h := congrArg (fun f : Polynomial (Polynomial K) => f.coeff 0) hBz
    rw [coeff_zero_twoFunctionFactorBzSeries ell hell] at h
    simpa using h
  have hZell :
      -(Polynomial.C 2 * Polynomial.C a * Polynomial.C b *
          Polynomial.C ((ell : K) + 1) * Q.derivative) +
        Polynomial.C b ^ 2 * Polynomial.C (ell : K) *
          P.derivative.derivative = 0 := by
    have h := congrArg (fun f : Polynomial (Polynomial K) => f.coeff ell) hBz
    rw [coeff_ell_twoFunctionFactorBzSeries ell hell] at h
    simpa using h
  exact twoFunction_factorB_coefficients_impossible
    ell hell a b ha hb P Q hQ1 hX0 hXell hZ0 hZell

end

end HC4.Polynomial
