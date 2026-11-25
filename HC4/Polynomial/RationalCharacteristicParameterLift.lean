import HC4.Polynomial.RationalCharacteristicRankOnePencil
import Mathlib.RingTheory.Polynomial.GaussLemma

/-!
# Reduced rational parameter trace lift

The kernel of evaluation at a reduced fraction p/q contains no
nonzero time polynomial whose source coefficients all have degree
strictly smaller than max(deg p, deg q).

Gauss's lemma descends the linear factor from the fraction field.
The leading or lowest surviving time coefficient of the resulting
product gives the degree contradiction. This avoids any assumption
that relatively prime multivariate polynomials are Bezout-coprime.

The rank-one parametrization and differentiation supplying the
evaluated trace equation are separate from this algebraic lift.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev T (K : Type*) [Field K] := _root_.Polynomial (B K)

/-- The reduced linear parameter polynomial is primitive, using
relative primality rather than a Bezout identity. -/
theorem rationalParameter_linear_isPrimitive
    (p q : B K) (hcop : IsRelPrime p q) :
    (_root_.Polynomial.C q * _root_.Polynomial.X -
      _root_.Polynomial.C p : T K).IsPrimitive := by
  apply _root_.Polynomial.isPrimitive_iff_isUnit_of_C_dvd.mpr
  intro r hr
  obtain ⟨f, hf⟩ := hr
  apply hcop
  · refine ⟨-f.coeff 0, ?_⟩
    have h := congrArg (fun F : T K => F.coeff 0) hf
    change (_root_.Polynomial.C q * _root_.Polynomial.X -
      _root_.Polynomial.C p : T K).coeff 0 =
      (_root_.Polynomial.C r * f).coeff 0 at h
    simp only [_root_.Polynomial.coeff_sub, _root_.Polynomial.coeff_mul_X_zero,
      _root_.Polynomial.coeff_C_zero, zero_sub, _root_.Polynomial.coeff_C_mul] at h
    calc
      p = -(r * f.coeff 0) := by rw [← h, neg_neg]
      _ = r * -f.coeff 0 := by ring
  · refine ⟨f.coeff 1, ?_⟩
    have h := congrArg (fun F : T K => F.coeff 1) hf
    change (_root_.Polynomial.C q * _root_.Polynomial.X -
      _root_.Polynomial.C p : T K).coeff 1 =
      (_root_.Polynomial.C r * f).coeff 1 at h
    simpa [_root_.Polynomial.coeff_sub, _root_.Polynomial.coeff_C_mul_X,
      _root_.Polynomial.coeff_C_mul] using h

/-- A polynomial relation at a reduced rational parameter is divisible
by its primitive linear defining polynomial over the source ring. -/
theorem rationalParameter_linear_dvd_of_eval_zero
    (p q : B K) (hq : q ≠ 0) (hcop : IsRelPrime p q) (F : T K)
    (hF : F.eval₂ (algebraMap (B K) (E K))
      (algebraMap (B K) (E K) p / algebraMap (B K) (E K) q) = 0) :
    (_root_.Polynomial.C q * _root_.Polynomial.X -
      _root_.Polynomial.C p : T K) ∣ F := by
  classical
  by_cases hf : F = 0
  · rw [hf]
    exact dvd_zero _
  let g : B K →+* E K := algebraMap (B K) (E K)
  let t : E K := g p / g q
  let L : T K := _root_.Polynomial.C q * _root_.Polynomial.X - _root_.Polynomial.C p
  have hgq : g q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hq
  have hprim : L.IsPrimitive := rationalParameter_linear_isPrimitive p q hcop
  have he : F.primPart.eval₂ g t = 0 :=
    _root_.Polynomial.eval₂_primPart_eq_zero (IsFractionRing.injective (B K) (E K)) hf hF
  have hroot : (_root_.Polynomial.X - _root_.Polynomial.C t) ∣ F.primPart.map g := by
    apply _root_.Polynomial.dvd_iff_isRoot.mpr
    change (F.primPart.map g).eval t = 0
    rw [_root_.Polynomial.eval_map]
    exact he
  have hqt : g q * t = g p := by
    rw [t, mul_comm, div_mul_cancel₀ _ hgq]
  have hL : L.map g = _root_.Polynomial.C (g q) *
      (_root_.Polynomial.X - _root_.Polynomial.C t) := by
    simp only [L, _root_.Polynomial.map_sub, _root_.Polynomial.map_mul,
      _root_.Polynomial.map_C, _root_.Polynomial.map_X, mul_sub,
      ← _root_.Polynomial.C_mul, hqt]
  have hdvd : L.map g ∣ F.primPart.map g := by
    obtain ⟨r, hr⟩ := hroot
    have hu : IsUnit (_root_.Polynomial.C (g q)) :=
      _root_.Polynomial.isUnit_C.mpr (isUnit_iff_ne_zero.mpr hgq)
    obtain ⟨s, hs⟩ : _root_.Polynomial.C (g q) ∣ r := hu.dvd
    refine ⟨s, ?_⟩
    rw [hL, hr, hs]
    ring
  have hd : L ∣ F.primPart :=
    hprim.dvd_of_fraction_map_dvd_fraction_map
      (_root_.Polynomial.isPrimitive_primPart F) hdvd
  exact (hprim.dvd_primPart_iff_dvd hf).mp hd

/-- A nonzero multiple of a reduced linear parameter polynomial has
a source coefficient at least as large in total degree as one of
the parameter polynomials. No cancellation can avoid both ends. -/
theorem rationalParameter_eq_zero_of_linear_dvd_of_small_coeff
    (p q : B K) (hq : q ≠ 0) (F : T K)
    (hdvd : (_root_.Polynomial.C q * _root_.Polynomial.X -
      _root_.Polynomial.C p : T K) ∣ F)
    (hsmall : ∀ n : ℕ, (F.coeff n).totalDegree <
      max p.totalDegree q.totalDegree) : F = 0 := by
  classical
  obtain ⟨R, hR⟩ := hdvd
  have hprod : F = _root_.Polynomial.X * (_root_.Polynomial.C q * R) -
      _root_.Polynomial.C p * R := by
    rw [hR]
    ring
  have hc0 : F.coeff 0 = -(p * R.coeff 0) := by
    rw [hprod, _root_.Polynomial.coeff_sub, _root_.Polynomial.coeff_X_mul_zero,
      zero_sub, _root_.Polynomial.coeff_C_mul]
  have hcs (n : ℕ) : F.coeff (n + 1) =
      q * R.coeff n - p * R.coeff (n + 1) := by
    rw [hprod, _root_.Polynomial.coeff_sub, _root_.Polynomial.coeff_X_mul,
      _root_.Polynomial.coeff_C_mul, _root_.Polynomial.coeff_C_mul]
  by_cases hdeg : q.totalDegree ≤ p.totalDegree
  · have hp : p ≠ 0 := by
      intro hp
      have h := hsmall 0
      rw [hp, MvPolynomial.totalDegree_zero] at hdeg h
      omega
    have hc : ∀ n : ℕ, R.coeff n = 0 := by
      intro n
      induction n with
      | zero =>
        by_contra hn
        have h := hsmall 0
        rw [max_eq_left hdeg, hc0, MvPolynomial.totalDegree_neg,
          MvPolynomial.totalDegree_mul_of_isDomain hp hn] at h
        omega
      | succ n ih =>
        by_contra hn
        have h := hsmall (n + 1)
        rw [max_eq_left hdeg, hcs n, ih, mul_zero, zero_sub,
          MvPolynomial.totalDegree_neg,
          MvPolynomial.totalDegree_mul_of_isDomain hp hn] at h
        omega
    have hz : R = 0 := by
      apply _root_.Polynomial.ext
      intro n
      rw [hc, _root_.Polynomial.coeff_zero]
    rw [hR, hz, mul_zero]
  · by_contra hf
    have hr : R ≠ 0 := by
      intro hr
      apply hf
      rw [hR, hr, mul_zero]
    have hn : R.coeff R.natDegree ≠ 0 := by
      rw [_root_.Polynomial.coeff_natDegree]
      exact _root_.Polynomial.leadingCoeff_ne_zero.mpr hr
    have hnext : R.coeff (R.natDegree + 1) = 0 :=
      _root_.Polynomial.coeff_natDegree_succ_eq_zero
    have h := hsmall (R.natDegree + 1)
    rw [max_eq_right (Nat.le_of_lt (Nat.lt_of_not_ge hdeg)), hcs, hnext,
      mul_zero, sub_zero, MvPolynomial.totalDegree_mul_of_isDomain hq hn] at h
    omega

/-- The lifted relation is identically zero when its source
coefficients are strictly below the reduced parameter degree. -/
theorem rationalParameter_lift_of_eval_zero
    (p q : B K) (hq : q ≠ 0) (hcop : IsRelPrime p q) (F : T K)
    (hF : F.eval₂ (algebraMap (B K) (E K))
      (algebraMap (B K) (E K) p / algebraMap (B K) (E K) q) = 0)
    (hsmall : ∀ n : ℕ, (F.coeff n).totalDegree <
      max p.totalDegree q.totalDegree) : F = 0 :=
  rationalParameter_eq_zero_of_linear_dvd_of_small_coeff p q hq F
    (rationalParameter_linear_dvd_of_eval_zero p q hq hcop F hF) hsmall

end
end HC4.Polynomial.RankThreeCubic
