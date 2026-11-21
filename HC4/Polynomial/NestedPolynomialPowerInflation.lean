import HC4.Polynomial.ComplementaryMvSubstitution
import Mathlib.Tactic

/-!
# Injective power inflation in two nested polynomial variables

The codimension-two Euler-Hessian bridge naturally lands in

    K[t][s] = Polynomial (Polynomial K).

We need to replace the abstract departure variables by positive powers

    s |-> s^m,
    t |-> t^n.

This file packages that substitution as a ring endomorphism and proves it is
injective for `m,n>0`.  It is independent of HC4 geometry.
-/

namespace HC4.Polynomial

noncomputable section

/-- Composition with `X^n` is injective over any integral commutative ring,
not only over a field. -/
theorem comp_X_pow_eq_zero_of_pos_domain
    {R : Type*} [CommRing R] [IsDomain R]
    {p : Polynomial R} {n : ℕ}
    (hn : 0 < n)
    (hzero : p.comp (Polynomial.X ^ n) = 0) :
    p = 0 := by
  rw [Polynomial.comp_eq_zero_iff] at hzero
  rcases hzero with hp | ⟨_heval, hconst⟩
  · exact hp
  · exfalso
    have h0n : 0 ≠ n := Nat.ne_of_lt hn
    have hcoeff0 : (Polynomial.X ^ n : Polynomial R).coeff 0 = 0 := by
      simp [h0n]
    have hpowzero : (Polynomial.X ^ n : Polynomial R) = 0 := by
      calc
        (Polynomial.X ^ n : Polynomial R) =
            Polynomial.C ((Polynomial.X ^ n : Polynomial R).coeff 0) := hconst
        _ = 0 := by rw [hcoeff0]; simp
    exact (pow_ne_zero n Polynomial.X_ne_zero) hpowzero

/-- Domain-level injectivity of positive power composition. -/
theorem comp_X_pow_injective_domain
    {R : Type*} [CommRing R] [IsDomain R]
    {n : ℕ} (hn : 0 < n) :
    Function.Injective (fun p : Polynomial R =>
      p.comp (Polynomial.X ^ n)) := by
  intro p q hpq
  have hz : (p - q).comp (Polynomial.X ^ n) = 0 := by
    rw [Polynomial.sub_comp, hpq, sub_self]
  have hpq0 := comp_X_pow_eq_zero_of_pos_domain hn hz
  exact sub_eq_zero.mp hpq0

/-- Inner-variable power substitution on `K[t]`. -/
noncomputable def innerPowerInflation
    {K : Type*} [Field K]
    (n : ℕ) : Polynomial K →+* Polynomial K :=
  (Polynomial.X ^ n).compRingHom

/-- Two-level substitution on `K[t][s]`: coefficients undergo `t |-> t^n`
and the outer variable undergoes `s |-> s^m`. -/
noncomputable def nestedPolynomialPowerInflation
    {K : Type*} [Field K]
    (m n : ℕ) :
    Polynomial (Polynomial K) →+* Polynomial (Polynomial K) :=
  ((Polynomial.X ^ m : Polynomial (Polynomial K)).compRingHom).comp
    (Polynomial.mapRingHom (innerPowerInflation (K := K) n))

@[simp] theorem innerPowerInflation_apply
    {K : Type*} [Field K]
    (n : ℕ) (p : Polynomial K) :
    innerPowerInflation (K := K) n p =
      p.comp (Polynomial.X ^ n) := by
  simpa [innerPowerInflation] using
    (Polynomial.coe_compRingHom_apply p (Polynomial.X ^ n))

@[simp] theorem nestedPolynomialPowerInflation_X
    {K : Type*} [Field K]
    (m n : ℕ) :
    nestedPolynomialPowerInflation (K := K) m n
        (Polynomial.X : Polynomial (Polynomial K)) =
      Polynomial.X ^ m := by
  simp [nestedPolynomialPowerInflation, innerPowerInflation]

@[simp] theorem nestedPolynomialPowerInflation_C_X
    {K : Type*} [Field K]
    (m n : ℕ) :
    nestedPolynomialPowerInflation (K := K) m n
        (Polynomial.C (Polynomial.X : Polynomial K)) =
      Polynomial.C (Polynomial.X ^ n) := by
  simp [nestedPolynomialPowerInflation, innerPowerInflation]

/-- Coefficientwise polynomial mapping is injective when the coefficient ring
homomorphism is injective. -/
theorem polynomial_map_injective_of_injective
    {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S)
    (hf : Function.Injective f) :
    Function.Injective (Polynomial.mapRingHom f) := by
  intro p q hpq
  ext k
  have hcoeff := congrArg (fun r : Polynomial S => r.coeff k) hpq
  simp only [Polynomial.coeff_map] at hcoeff
  exact hf hcoeff

/-- Positive nested power inflation is injective. -/
theorem nestedPolynomialPowerInflation_injective
    {K : Type*} [Field K]
    {m n : ℕ}
    (hm : 0 < m) (hn : 0 < n) :
    Function.Injective
      (nestedPolynomialPowerInflation (K := K) m n) := by
  let inner : Polynomial K →+* Polynomial K :=
    innerPowerInflation (K := K) n
  have hinner : Function.Injective inner := by
    intro p q hpq
    change p.comp (Polynomial.X ^ n) = q.comp (Polynomial.X ^ n) at hpq
    exact comp_X_pow_injective_domain hn hpq
  have hmap :
      Function.Injective (Polynomial.mapRingHom inner) :=
    polynomial_map_injective_of_injective inner hinner
  have houter :
      Function.Injective
        (fun p : Polynomial (Polynomial K) =>
          p.comp (Polynomial.X ^ m)) :=
    comp_X_pow_injective_domain hm
  intro p q hpq
  apply hmap
  apply houter
  change
    ((Polynomial.X ^ m : Polynomial (Polynomial K)).compRingHom)
        (Polynomial.mapRingHom inner p) =
      ((Polynomial.X ^ m : Polynomial (Polynomial K)).compRingHom)
        (Polynomial.mapRingHom inner q)
  simpa [nestedPolynomialPowerInflation, inner] using hpq

end

end HC4.Polynomial
