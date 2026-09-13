import HC4.Polynomial.TwoFunctionEulerCalculus
import HC4.Polynomial.TwoFunctionEulerRigidity
import Mathlib.Tactic

/-!
# Concrete rigidity for the two-function Euler factor

This file connects the abstract coefficient contradiction in
`TwoFunctionEulerRigidity` to the actual multivariate second factor of the
no-singleton carrier.

There are two deliberately simple extraction moves:

* differentiate in coordinate `0` to isolate the coefficient of `x`;
* specialise `x=1, y=X, z=0, w=1` to set `Y=X` and `H=0`.

The first move separates the `x` and `z` coefficients of `B`; the second
separates the constant and `H^ell` terms in each coefficient.  No Laurent
polynomials and no coefficient copying are used.
-/

namespace HC4.Polynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- Honest specialisation used to read the `H=0` coefficient while retaining
`Y` as a free one-variable polynomial. -/
def twoFunctionYSpecialisation :
    MvPolynomial (Fin 4) K →+* Polynomial K :=
  MvPolynomial.eval₂Hom Polynomial.C
    ![(1 : Polynomial K), Polynomial.X, 0, 1]

@[simp] theorem twoFunctionYSpecialisation_Y (V : ℕ) :
    twoFunctionYSpecialisation (K := K) (twoFunctionY (K := K) V) =
      Polynomial.X := by
  simp [twoFunctionYSpecialisation, twoFunctionY]

@[simp] theorem twoFunctionYSpecialisation_H (V : ℕ) :
    twoFunctionYSpecialisation (K := K) (twoFunctionH (K := K) V) = 0 := by
  simp [twoFunctionYSpecialisation, twoFunctionH]

/-- The `Y`-lift is split by the honest specialisation. -/
@[simp] theorem twoFunctionYSpecialisation_polynomialLift
    (V : ℕ) (p : Polynomial K) :
    twoFunctionYSpecialisation (K := K)
        (polynomialLift (twoFunctionY (K := K) V) p) = p := by
  unfold twoFunctionYSpecialisation polynomialLift
  rw [Polynomial.hom_eval₂]
  simp [twoFunctionY]

/-- Consequently substitution at the transcendental monomial `Y=yw^V` is
injective. -/
theorem polynomial_eq_zero_of_twoFunctionY_lift_eq_zero
    (V : ℕ) (p : Polynomial K)
    (h : polynomialLift (twoFunctionY (K := K) V) p = 0) :
    p = 0 := by
  have hs := congrArg (twoFunctionYSpecialisation (K := K)) h
  simpa using hs

/-- The coefficient of `x` in the concrete second Euler factor. -/
def twoFunctionConcreteBx
    (V ell : ℕ) (b : K) (Q : Polynomial K) :
    MvPolynomial (Fin 4) K :=
  let Y := twoFunctionY (K := K) V
  let H := twoFunctionH (K := K) V
  let q1 := polynomialLift Y Q.derivative
  let q2 := polynomialLift Y Q.derivative.derivative
  MvPolynomial.C b * MvPolynomial.C ((ell : K) - 1) * q1 ^ 2 +
    MvPolynomial.C b ^ 2 * MvPolynomial.C (ell : K) * H ^ ell * q2

/-- The coefficient of `z` in the concrete second Euler factor. -/
def twoFunctionConcreteBz
    (V ell : ℕ) (a b : K) (P Q : Polynomial K) :
    MvPolynomial (Fin 4) K :=
  let Y := twoFunctionY (K := K) V
  let H := twoFunctionH (K := K) V
  let q1 := polynomialLift Y Q.derivative
  let p1 := polynomialLift Y P.derivative
  let p2 := polynomialLift Y P.derivative.derivative
  MvPolynomial.C a * MvPolynomial.C ((ell : K) + 1) * Y * q1 ^ 2 -
      MvPolynomial.C 2 * MvPolynomial.C b * p1 * q1 -
    MvPolynomial.C 2 * MvPolynomial.C a * MvPolynomial.C b *
        MvPolynomial.C ((ell : K) + 1) * H ^ ell * q1 +
    MvPolynomial.C b ^ 2 * MvPolynomial.C (ell : K) * H ^ ell * p2

/-- The abstract concrete `B` factor is literally linear in `x,z` with the
two coefficients above. -/
theorem twoFunctionEulerFactorB_eq_xBx_add_zBz
    (V ell : ℕ) (a b : K) (P Q : Polynomial K) :
    twoFunctionEulerFactorB
        V ell
        (MvPolynomial.X (0 : Fin 4))
        (MvPolynomial.X (2 : Fin 4))
        (twoFunctionY (K := K) V)
        (twoFunctionH (K := K) V)
        (MvPolynomial.C a)
        (MvPolynomial.C b)
        (polynomialLift (twoFunctionY (K := K) V) Q.derivative)
        (polynomialLift (twoFunctionY (K := K) V) Q.derivative.derivative)
        (polynomialLift (twoFunctionY (K := K) V) P.derivative)
        (polynomialLift (twoFunctionY (K := K) V) P.derivative.derivative) =
      MvPolynomial.X (0 : Fin 4) * twoFunctionConcreteBx V ell b Q +
        MvPolynomial.X (2 : Fin 4) * twoFunctionConcreteBz V ell a b P Q := by
  simp [twoFunctionEulerFactorB, twoFunctionConcreteBx,
    twoFunctionConcreteBz]
  ring

/-- Differentiation in `x` reads off the `Bx` coefficient exactly. -/
theorem pderiv_zero_twoFunctionEulerFactorB
    (V ell : ℕ) (a b : K) (P Q : Polynomial K) :
    MvPolynomial.pderiv (0 : Fin 4)
      (twoFunctionEulerFactorB
        V ell
        (MvPolynomial.X (0 : Fin 4))
        (MvPolynomial.X (2 : Fin 4))
        (twoFunctionY (K := K) V)
        (twoFunctionH (K := K) V)
        (MvPolynomial.C a)
        (MvPolynomial.C b)
        (polynomialLift (twoFunctionY (K := K) V) Q.derivative)
        (polynomialLift (twoFunctionY (K := K) V) Q.derivative.derivative)
        (polynomialLift (twoFunctionY (K := K) V) P.derivative)
        (polynomialLift (twoFunctionY (K := K) V) P.derivative.derivative)) =
      twoFunctionConcreteBx V ell b Q := by
  rw [twoFunctionEulerFactorB_eq_xBx_add_zBz]
  simp [twoFunctionConcreteBx, twoFunctionConcreteBz,
    twoFunctionY, twoFunctionH, polynomialLift,
    MvPolynomial.pderiv_mul, MvPolynomial.pderiv_pow]

/-- A zero concrete `B` factor forces its `x` coefficient to vanish. -/
theorem twoFunctionConcreteBx_eq_zero_of_factorB_eq_zero
    (V ell : ℕ) (a b : K) (P Q : Polynomial K)
    (hB :
      twoFunctionEulerFactorB
        V ell
        (MvPolynomial.X (0 : Fin 4))
        (MvPolynomial.X (2 : Fin 4))
        (twoFunctionY (K := K) V)
        (twoFunctionH (K := K) V)
        (MvPolynomial.C a)
        (MvPolynomial.C b)
        (polynomialLift (twoFunctionY (K := K) V) Q.derivative)
        (polynomialLift (twoFunctionY (K := K) V) Q.derivative.derivative)
        (polynomialLift (twoFunctionY (K := K) V) P.derivative)
        (polynomialLift (twoFunctionY (K := K) V) P.derivative.derivative) = 0) :
    twoFunctionConcreteBx V ell b Q = 0 := by
  have h := congrArg (MvPolynomial.pderiv (0 : Fin 4)) hB
  rw [pderiv_zero_twoFunctionEulerFactorB] at h
  simpa using h

/-- A zero concrete `B` factor also forces its `z` coefficient to vanish. -/
theorem twoFunctionConcreteBz_eq_zero_of_factorB_eq_zero
    (V ell : ℕ) (a b : K) (P Q : Polynomial K)
    (hB :
      twoFunctionEulerFactorB
        V ell
        (MvPolynomial.X (0 : Fin 4))
        (MvPolynomial.X (2 : Fin 4))
        (twoFunctionY (K := K) V)
        (twoFunctionH (K := K) V)
        (MvPolynomial.C a)
        (MvPolynomial.C b)
        (polynomialLift (twoFunctionY (K := K) V) Q.derivative)
        (polynomialLift (twoFunctionY (K := K) V) Q.derivative.derivative)
        (polynomialLift (twoFunctionY (K := K) V) P.derivative)
        (polynomialLift (twoFunctionY (K := K) V) P.derivative.derivative) = 0) :
    twoFunctionConcreteBz V ell a b P Q = 0 := by
  have hBx := twoFunctionConcreteBx_eq_zero_of_factorB_eq_zero
    V ell a b P Q hB
  rw [twoFunctionEulerFactorB_eq_xBx_add_zBz, hBx] at hB
  simp only [mul_zero, zero_add] at hB
  exact (mul_eq_zero.mp hB).resolve_left MvPolynomial.X_ne_zero

/-- The constant `H` coefficient equation of `Bx`. -/
theorem twoFunctionConcreteBx_constant_eq_zero
    (V ell : ℕ) (hell : 0 < ell) (b : K) (Q : Polynomial K)
    (hBx : twoFunctionConcreteBx V ell b Q = 0) :
    Polynomial.C b * Polynomial.C ((ell : K) - 1) * Q.derivative ^ 2 = 0 := by
  have h := congrArg (twoFunctionYSpecialisation (K := K)) hBx
  simpa [twoFunctionConcreteBx, hell.ne'] using h

/-- The top `H^ell` coefficient equation of `Bx`. -/
theorem twoFunctionConcreteBx_top_eq_zero
    (V ell : ℕ) (hell : 0 < ell) (b : K) (Q : Polynomial K)
    (hBx : twoFunctionConcreteBx V ell b Q = 0) :
    Polynomial.C b ^ 2 * Polynomial.C (ell : K) *
        Q.derivative.derivative = 0 := by
  let f : Polynomial K :=
    Polynomial.C b * Polynomial.C ((ell : K) - 1) * Q.derivative ^ 2
  let g : Polynomial K :=
    Polynomial.C b ^ 2 * Polynomial.C (ell : K) * Q.derivative.derivative
  have hf : f = 0 := by
    dsimp [f]
    exact twoFunctionConcreteBx_constant_eq_zero V ell hell b Q hBx
  have hdecomp :
      twoFunctionConcreteBx V ell b Q =
        polynomialLift (twoFunctionY (K := K) V) f +
          twoFunctionH (K := K) V ^ ell *
            polynomialLift (twoFunctionY (K := K) V) g := by
    simp [twoFunctionConcreteBx, f, g, polynomialLift]
    ring
  have hprod :
      twoFunctionH (K := K) V ^ ell *
          polynomialLift (twoFunctionY (K := K) V) g = 0 := by
    rw [hdecomp] at hBx
    rw [hf] at hBx
    simpa using hBx
  have hHne : twoFunctionH (K := K) V ≠ 0 := by
    apply mul_ne_zero MvPolynomial.X_ne_zero
    exact pow_ne_zero _ MvPolynomial.X_ne_zero
  have hglift : polynomialLift (twoFunctionY (K := K) V) g = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero ell hHne)
  have hg : g = 0 :=
    polynomial_eq_zero_of_twoFunctionY_lift_eq_zero V g hglift
  simpa [g] using hg

/-- The constant `H` coefficient equation of `Bz`. -/
theorem twoFunctionConcreteBz_constant_eq_zero
    (V ell : ℕ) (hell : 0 < ell) (a b : K) (P Q : Polynomial K)
    (hBz : twoFunctionConcreteBz V ell a b P Q = 0) :
    Polynomial.C a * Polynomial.C ((ell : K) + 1) * Polynomial.X *
          Q.derivative ^ 2 -
        Polynomial.C 2 * Polynomial.C b * P.derivative * Q.derivative = 0 := by
  have h := congrArg (twoFunctionYSpecialisation (K := K)) hBz
  simpa [twoFunctionConcreteBz, hell.ne'] using h

/-- The top `H^ell` coefficient equation of `Bz`. -/
theorem twoFunctionConcreteBz_top_eq_zero
    (V ell : ℕ) (hell : 0 < ell) (a b : K) (P Q : Polynomial K)
    (hBz : twoFunctionConcreteBz V ell a b P Q = 0) :
    -(Polynomial.C 2 * Polynomial.C a * Polynomial.C b *
          Polynomial.C ((ell : K) + 1) * Q.derivative) +
        Polynomial.C b ^ 2 * Polynomial.C (ell : K) *
          P.derivative.derivative = 0 := by
  let f : Polynomial K :=
    Polynomial.C a * Polynomial.C ((ell : K) + 1) * Polynomial.X *
          Q.derivative ^ 2 -
        Polynomial.C 2 * Polynomial.C b * P.derivative * Q.derivative
  let g : Polynomial K :=
    -(Polynomial.C 2 * Polynomial.C a * Polynomial.C b *
          Polynomial.C ((ell : K) + 1) * Q.derivative) +
        Polynomial.C b ^ 2 * Polynomial.C (ell : K) *
          P.derivative.derivative
  have hf : f = 0 := by
    dsimp [f]
    exact twoFunctionConcreteBz_constant_eq_zero V ell hell a b P Q hBz
  have hdecomp :
      twoFunctionConcreteBz V ell a b P Q =
        polynomialLift (twoFunctionY (K := K) V) f +
          twoFunctionH (K := K) V ^ ell *
            polynomialLift (twoFunctionY (K := K) V) g := by
    simp [twoFunctionConcreteBz, f, g, polynomialLift]
    ring
  have hprod :
      twoFunctionH (K := K) V ^ ell *
          polynomialLift (twoFunctionY (K := K) V) g = 0 := by
    rw [hdecomp] at hBz
    rw [hf] at hBz
    simpa using hBz
  have hHne : twoFunctionH (K := K) V ≠ 0 := by
    apply mul_ne_zero MvPolynomial.X_ne_zero
    exact pow_ne_zero _ MvPolynomial.X_ne_zero
  have hglift : polynomialLift (twoFunctionY (K := K) V) g = 0 :=
    (mul_eq_zero.mp hprod).resolve_left (pow_ne_zero ell hHne)
  have hg : g = 0 :=
    polynomial_eq_zero_of_twoFunctionY_lift_eq_zero V g hglift
  simpa [g] using hg

/-- **Concrete second-factor impossibility.**  Under the nondegeneracy
hypotheses from the source geometry, the actual multivariate `B` factor cannot
vanish. -/
theorem twoFunction_concrete_factorB_impossible
    (V ell : ℕ) (hell : 0 < ell)
    (a b : K) (ha : a ≠ 0) (hb : b ≠ 0)
    (P Q : Polynomial K) (hQ1 : Q.derivative ≠ 0)
    (hB :
      twoFunctionEulerFactorB
        V ell
        (MvPolynomial.X (0 : Fin 4))
        (MvPolynomial.X (2 : Fin 4))
        (twoFunctionY (K := K) V)
        (twoFunctionH (K := K) V)
        (MvPolynomial.C a)
        (MvPolynomial.C b)
        (polynomialLift (twoFunctionY (K := K) V) Q.derivative)
        (polynomialLift (twoFunctionY (K := K) V) Q.derivative.derivative)
        (polynomialLift (twoFunctionY (K := K) V) P.derivative)
        (polynomialLift (twoFunctionY (K := K) V) P.derivative.derivative) = 0) :
    False := by
  have hBx := twoFunctionConcreteBx_eq_zero_of_factorB_eq_zero
    V ell a b P Q hB
  have hBz := twoFunctionConcreteBz_eq_zero_of_factorB_eq_zero
    V ell a b P Q hB
  have hX0 := twoFunctionConcreteBx_constant_eq_zero V ell hell b Q hBx
  have hXell := twoFunctionConcreteBx_top_eq_zero V ell hell b Q hBx
  have hZ0 := twoFunctionConcreteBz_constant_eq_zero V ell hell a b P Q hBz
  have hZell := twoFunctionConcreteBz_top_eq_zero V ell hell a b P Q hBz
  exact twoFunction_factorB_coefficients_impossible
    ell hell a b ha hb P Q hQ1 hX0 hXell hZ0 hZell

end

end HC4.Polynomial
