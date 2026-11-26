module

public import HC4.Polynomial.RankThreeCubicRepeatedPoleLinearCofactor
public import Mathlib.Tactic

/-!
# Uniqueness of the genuine cubic source denominator pole

The local source/Jacobi theorem says every genuine reduced-denominator
pole factor occurs with multiplicity at least two in det(H).

Since det(H) has total degree at most three, two distinct irreducible
factors cannot both occur with multiplicity two. This identifies a
*unique associated prime class* for genuine pole factors of all
characteristic coordinates. It does not eliminate that last pole.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

namespace RankThreeCubicUniqueGenuinePole

abbrev B3 (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev F3 (K : Type*) [Field K] := FractionRing (B3 K)
abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

end RankThreeCubicUniqueGenuinePole

open RankThreeCubicUniqueGenuinePole (B3 F3 SB)

/-- In a nonzero cubic polynomial, any two irreducible factors whose
squares divide the polynomial are associated. Here is the one-sided
divisibility statement, avoiding a factorization normalization. -/
theorem repeated_prime_dvd_repeated_prime_of_cubic_degree
    (D p q : B3 K)
    (hD : D ≠ 0)
    (hdeg : D.totalDegree ≤ 3)
    (hp : Irreducible p)
    (hq : Irreducible q)
    (hpp : p * p ∣ D)
    (hqq : q * q ∣ D) :
    q ∣ p := by
  classical
  obtain ⟨c, hfact, hc0, hcdeg⟩ :=
    cubic_repeatedFactor_has_linear_cofactor D p hD hdeg hp hpp
  by_contra hqp
  have hrel : IsRelPrime q p :=
    hq.isRelPrime_iff_not_dvd.mpr hqp
  have hrel2 : IsRelPrime (q * q) (p * p) := by
    simpa only [pow_two] using (hrel.pow (m := 2) (n := 2))
  have hqq' : (q * q) ∣ (p * p) * c := by
    simpa only [hfact] using hqq
  have hqc : (q * q) ∣ c :=
    hrel2.dvd_of_dvd_mul_left hqq'
  have hqdeg : q.totalDegree = 1 :=
    degree_one_of_specified_repeated_factor D q hD hdeg hq hqq
  have hq2deg : (q * q).totalDegree = 2 := by
    rw [MvPolynomial.totalDegree_mul_of_isDomain hq.ne_zero hq.ne_zero,
      hqdeg]
  have hle : (q * q).totalDegree ≤ c.totalDegree := by
    obtain ⟨u, hu⟩ := hqc
    have hu0 : u ≠ 0 := by
      intro hz
      apply hc0
      rw [hu, hz, mul_zero]
    have hmul : c.totalDegree = (q * q).totalDegree + u.totalDegree := by
      rw [hu]
      exact MvPolynomial.totalDegree_mul_of_isDomain
        (mul_ne_zero hq.ne_zero hq.ne_zero) hu0
    omega
  omega

/-- Uniqueness of the repeated irreducible cubic factor, up to
association. In particular the cubic has at most one double factor. -/
theorem repeated_irreducible_factors_associated_of_cubic_degree
    (D p q : B3 K)
    (hD : D ≠ 0)
    (hdeg : D.totalDegree ≤ 3)
    (hp : Irreducible p)
    (hq : Irreducible q)
    (hpp : p * p ∣ D)
    (hqq : q * q ∣ D) :
    Associated p q := by
  have hpq : p ∣ q :=
    repeated_prime_dvd_repeated_prime_of_cubic_degree
      D q p hD hdeg hq hp hqq hpp
  have hqp : q ∣ p :=
    repeated_prime_dvd_repeated_prime_of_cubic_degree
      D p q hD hdeg hp hq hpp hqq
  exact associated_of_dvd_dvd hpq hqp

/-- Two actual non-cancelled reduced-coordinate denominator primes
of the same source cubic characteristic must be associated.

Both poles are selected from the original characteristic, with no
added squarefree, rank, or terminal endpoint assumptions. -/
theorem sourceCubic_genuinePole_primes_associated
    (F : SB K) (a : K)
    (V : Unit ⊕ Fin 3 → F3 K)
    (hV : V (.inl ()) = 1)
    (hgrad :
      ∀ i : Unit ⊕ Fin 3,
        lineEval (transverseGenericPoint a) V
            (pderiv i (initialForm transverseCubicWeight 3 F)) =
          _root_.Polynomial.C
            (MvPolynomial.aeval (transverseGenericPoint a)
              (pderiv i (initialForm transverseCubicWeight 3 F))))
    (hreg : (sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F)).det ≠ 0)
    (i j : Fin 3) (p q : B3 K)
    (hp : Irreducible p) (hq : Irreducible q)
    (hpd : p ∣ (IsFractionRing.den (B3 K) (V (.inr i)) : B3 K))
    (hpn : ¬ p ∣ IsFractionRing.num (B3 K) (V (.inr i)))
    (hqd : q ∣ (IsFractionRing.den (B3 K) (V (.inr j)) : B3 K))
    (hqn : ¬ q ∣ IsFractionRing.num (B3 K) (V (.inr j))) :
    Associated p q := by
  have hpp : p * p ∣
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det :=
    sourceCubic_genuinePole_is_repeatedFactor
      F a V hV hgrad i p hp hpd hpn
  have hqq : q * q ∣
      (sourceTransverseHessian a
        (initialForm transverseCubicWeight 3 F)).det :=
    sourceCubic_genuinePole_is_repeatedFactor
      F a V hV hgrad j q hq hqd hqn
  exact repeated_irreducible_factors_associated_of_cubic_degree
    (sourceTransverseHessian a
      (initialForm transverseCubicWeight 3 F)).det
    p q hreg
    (sourceCubic_transverseHessian_det_homogeneous_three a F).totalDegree_le
    hp hq hpp hqq

end
end HC4.Polynomial.RankThreeCubic
