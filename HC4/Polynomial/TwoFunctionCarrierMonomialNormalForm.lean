import HC4.Polynomial.TwoFunctionEulerCalculus
import Mathlib.Tactic

/-!
# Monomial normal form of the concrete two-function carrier

For the A19 reconstruction it is useful to separate the finite-support
bookkeeping from the Hessian calculation.  When `P` and `Q` are single
univariate monomials, `twoFunctionCarrier` is literally a four-monomial
polynomial.  This file records that expansion with canonical `Fin 4` exponent
vectors.
-/

namespace HC4.Polynomial

noncomputable section

/-- Exponent of `Y = y w^V`. -/
def twoFunctionYExponent (V : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single (1 : Fin 4) 1 + Finsupp.single (3 : Fin 4) V

/-- Exponent of `H = z w^V`. -/
def twoFunctionHExponent (V : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single (2 : Fin 4) 1 + Finsupp.single (3 : Fin 4) V

/-- Locked `z H^ell Y` exponent. -/
def twoFunctionLockedFacetExponent (V ell : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single (2 : Fin 4) 1 +
    ell • twoFunctionHExponent V + twoFunctionYExponent V

/-- Locked `x H^ell` exponent. -/
def twoFunctionLockedOutsideExponent (V ell : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single (0 : Fin 4) 1 + ell • twoFunctionHExponent V

/-- Highest `z Y^n` exponent. -/
def twoFunctionHighestZExponent (V n : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single (2 : Fin 4) 1 + n • twoFunctionYExponent V

/-- Highest `x Y^(n-1)` exponent. -/
def twoFunctionHighestXExponent (V n : ℕ) : Fin 4 →₀ ℕ :=
  Finsupp.single (0 : Fin 4) 1 + (n - 1) • twoFunctionYExponent V

@[simp] theorem twoFunctionY_eq_monomial
    {K : Type*} [CommRing K] (V : ℕ) :
    twoFunctionY (K := K) V =
      MvPolynomial.monomial (twoFunctionYExponent V) 1 := by
  unfold twoFunctionY twoFunctionYExponent
  rw [MvPolynomial.X_pow_eq_monomial]
  change
    MvPolynomial.monomial (Finsupp.single (1 : Fin 4) 1) (1 : K) *
      MvPolynomial.monomial (Finsupp.single (3 : Fin 4) V) (1 : K) = _
  rw [MvPolynomial.monomial_mul_monomial]
  simp

@[simp] theorem twoFunctionH_eq_monomial
    {K : Type*} [CommRing K] (V : ℕ) :
    twoFunctionH (K := K) V =
      MvPolynomial.monomial (twoFunctionHExponent V) 1 := by
  unfold twoFunctionH twoFunctionHExponent
  rw [MvPolynomial.X_pow_eq_monomial]
  change
    MvPolynomial.monomial (Finsupp.single (2 : Fin 4) 1) (1 : K) *
      MvPolynomial.monomial (Finsupp.single (3 : Fin 4) V) (1 : K) = _
  rw [MvPolynomial.monomial_mul_monomial]
  simp

@[simp] theorem polynomialLift_monomial
    {K : Type*} [CommRing K]
    (t : MvPolynomial (Fin 4) K) (n : ℕ) (c : K) :
    polynomialLift t (Polynomial.monomial n c) =
      MvPolynomial.C c * t ^ n := by
  simp [polynomialLift]

private theorem X_eq_monomial
    {K : Type*} [CommRing K] (i : Fin 4) :
    (MvPolynomial.X i : MvPolynomial (Fin 4) K) =
      MvPolynomial.monomial (Finsupp.single i 1) 1 := by
  rfl

/-- `z H^ell Y` is one monomial with the canonical locked-facet exponent. -/
theorem X_two_mul_H_pow_mul_Y_eq_monomial
    {K : Type*} [CommRing K] (V ell : ℕ) (a : K) :
    MvPolynomial.X (2 : Fin 4) *
        (MvPolynomial.C a * twoFunctionH (K := K) V ^ ell *
          twoFunctionY (K := K) V) =
      MvPolynomial.monomial (twoFunctionLockedFacetExponent V ell) a := by
  rw [twoFunctionY_eq_monomial, twoFunctionH_eq_monomial,
    MvPolynomial.monomial_pow, X_eq_monomial]
  change
    MvPolynomial.monomial (Finsupp.single (2 : Fin 4) 1) (1 : K) *
      (MvPolynomial.monomial 0 a *
        MvPolynomial.monomial (ell • twoFunctionHExponent V) 1 *
        MvPolynomial.monomial (twoFunctionYExponent V) 1) = _
  simp [twoFunctionLockedFacetExponent, add_assoc]

/-- `x H^ell` is the locked outside monomial. -/
theorem X_zero_mul_H_pow_eq_monomial
    {K : Type*} [CommRing K] (V ell : ℕ) (b : K) :
    MvPolynomial.X (0 : Fin 4) *
        (MvPolynomial.C b * twoFunctionH (K := K) V ^ ell) =
      MvPolynomial.monomial (twoFunctionLockedOutsideExponent V ell) b := by
  rw [twoFunctionH_eq_monomial, MvPolynomial.monomial_pow, X_eq_monomial]
  change
    MvPolynomial.monomial (Finsupp.single (0 : Fin 4) 1) (1 : K) *
      (MvPolynomial.monomial 0 b *
        MvPolynomial.monomial (ell • twoFunctionHExponent V) 1) = _
  simp [twoFunctionLockedOutsideExponent, add_assoc]

/-- `z P(Y)` for a pure degree-`n` `P` is the highest `z Y^n` monomial. -/
theorem X_two_mul_polynomialLift_monomial_eq
    {K : Type*} [CommRing K] (V n : ℕ) (p : K) :
    MvPolynomial.X (2 : Fin 4) *
        polynomialLift (twoFunctionY (K := K) V) (Polynomial.monomial n p) =
      MvPolynomial.monomial (twoFunctionHighestZExponent V n) p := by
  rw [polynomialLift_monomial, twoFunctionY_eq_monomial,
    MvPolynomial.monomial_pow, X_eq_monomial]
  change
    MvPolynomial.monomial (Finsupp.single (2 : Fin 4) 1) (1 : K) *
      (MvPolynomial.monomial 0 p *
        MvPolynomial.monomial (n • twoFunctionYExponent V) 1) = _
  simp [twoFunctionHighestZExponent, add_assoc]

/-- `x Q(Y)` for pure degree `n-1` `Q` is the highest `x Y^(n-1)` monomial. -/
theorem X_zero_mul_polynomialLift_monomial_eq
    {K : Type*} [CommRing K] (V n : ℕ) (q : K) :
    MvPolynomial.X (0 : Fin 4) *
        polynomialLift (twoFunctionY (K := K) V)
          (Polynomial.monomial (n - 1) q) =
      MvPolynomial.monomial (twoFunctionHighestXExponent V n) q := by
  rw [polynomialLift_monomial, twoFunctionY_eq_monomial,
    MvPolynomial.monomial_pow, X_eq_monomial]
  change
    MvPolynomial.monomial (Finsupp.single (0 : Fin 4) 1) (1 : K) *
      (MvPolynomial.monomial 0 q *
        MvPolynomial.monomial ((n - 1) • twoFunctionYExponent V) 1) = _
  simp [twoFunctionHighestXExponent, add_assoc]

/-- **Four-monomial normal form.** -/
theorem twoFunctionCarrier_monomial_normalForm
    {K : Type*} [CommRing K]
    (V ell n : ℕ) (a b p q : K) :
    twoFunctionCarrier V ell a b
        (Polynomial.monomial n p)
        (Polynomial.monomial (n - 1) q) =
      MvPolynomial.monomial (twoFunctionLockedFacetExponent V ell) a +
      MvPolynomial.monomial (twoFunctionLockedOutsideExponent V ell) b +
      MvPolynomial.monomial (twoFunctionHighestZExponent V n) p +
      MvPolynomial.monomial (twoFunctionHighestXExponent V n) q := by
  unfold twoFunctionCarrier
  rw [mul_add, mul_add]
  rw [X_zero_mul_polynomialLift_monomial_eq,
    X_zero_mul_H_pow_eq_monomial,
    X_two_mul_polynomialLift_monomial_eq,
    X_two_mul_H_pow_mul_Y_eq_monomial]
  ring

end

end HC4.Polynomial
