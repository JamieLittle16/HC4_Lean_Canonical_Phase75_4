import HC4.Polynomial.RationalCharacteristicRankOneInvariantField

/-!
# Polynomial differential equations for invariant fractions

Clearing a corrected derivative gives a polynomial derivation.
For any invariant rational function, each member of its reduced
numerator/denominator pair divides its own corrected derivative.
This reduces the specialization issue to polynomial differential
equations, without a local-ring construction.

The nonvanishing theorem for solutions of those equations along
a noncharacteristic coordinate line is a separate obligation.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev I := Unit ⊕ Fin 3

/-- Polynomial action of a cleared corrected transverse derivative.
The fraction-field extension below is a genuine derivation; the
divisibility argument needs only this explicit polynomial action. -/
def rankOne_clearedPolynomialPartial
    (a b : B K) (j l : Fin 3) (p : B K) : B K :=
  b * pderiv l p - a * pderiv j p

theorem rankOne_clearedPolynomialPartial_algebraMap
    (a b : B K) (j l : Fin 3) (p : B K) :
    algebraMap (B K) (E K) (rankOne_clearedPolynomialPartial a b j l p) =
      algebraMap (B K) (E K) b *
        rationalCharacteristicPartial l (algebraMap (B K) (E K) p) -
      algebraMap (B K) (E K) a *
        rationalCharacteristicPartial j (algebraMap (B K) (E K) p) := by
  change algebraMap (B K) (E K) (b * pderiv l p - a * pderiv j p) = _
  rw [map_sub, map_mul, map_mul, rationalCharacteristicPartial_algebraMap,
    rationalCharacteristicPartial_algebraMap]

/-- An invariant fraction satisfies the cleared quotient equation
for any polynomial action agreeing with a fraction-field
derivation that kills that fraction. -/
theorem rationalInvariant_reducedPair_dvd
    (D : B K → B K)
    (D' : Derivation K (E K) (E K))
    (hD : ∀ f : B K, D' (algebraMap (B K) (E K) f) =
      algebraMap (B K) (E K) (D f))
    (p q : B K) (hq : q ≠ 0) (hcop : IsRelPrime p q)
    (hz : D' (algebraMap (B K) (E K) p /
      algebraMap (B K) (E K) q) = 0) :
    p ∣ D p ∧ q ∣ D q := by
  let e := algebraMap (B K) (E K)
  let z := e p / e q
  have hqe : e q ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hq
  have hmul : z * e q = e p := div_mul_cancel₀ _ hqe
  have h := congrArg D' hmul
  change D' (z * e q) = D' (e p) at h
  rw [Derivation.leibniz, hz, smul_zero, add_zero, hD, hD] at h
  change z * e (D q) = e (D p) at h
  have hc : D p * q = D q * p := by
    apply IsFractionRing.injective (B K) (E K)
    change e (D p * q) = e (D q * p)
    simp only [map_mul]
    calc
      e (D p) * e q = (z * e (D q)) * e q := by rw [h]
      _ = e (D q) * (z * e q) := by ring
      _ = e (D q) * e p := by rw [hmul]
  constructor
  · apply hcop.dvd_of_dvd_mul_right
    refine ⟨D q, ?_⟩
    exact hc.trans (mul_comm _ _)
  · apply hcop.symm.dvd_of_dvd_mul_right
    refine ⟨D p, ?_⟩
    exact hc.symm.trans (mul_comm _ _)

/-- For the actual velocity field the corrected differential
equations descend to both polynomials in any reduced fraction. -/
theorem rankOne_velocityField_reducedPair_dvd
    (V : I → E K) (i j l : Fin 3)
    (hp : rationalCharacteristicJacobian V i j ≠ 0)
    (hm : ∀ a b : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b)
    (a b p q : B K) (hb : b ≠ 0)
    (hab : algebraMap (B K) (E K) a / algebraMap (B K) (E K) b =
      rationalCharacteristicJacobian V i l / rationalCharacteristicJacobian V i j)
    (hq : q ≠ 0) (hcop : IsRelPrime p q)
    (hz : algebraMap (B K) (E K) p / algebraMap (B K) (E K) q ∈
      IntermediateField.adjoin K (Set.range (fun a : Fin 3 => V (.inr a)))) :
    p ∣ rankOne_clearedPolynomialPartial a b j l p ∧
      q ∣ rankOne_clearedPolynomialPartial a b j l q := by
  let e := algebraMap (B K) (E K)
  let D := rankOne_clearedPolynomialPartial a b j l
  let D' : Derivation K (E K) (E K) := e b • rationalCharacteristicPartial l -
    e a • rationalCharacteristicPartial j
  have hbe : e b ≠ 0 := by
    simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hb
  have hscale (z : E K) :
      D' z = e b * rankOne_correctedPartial V i j l z := by
    change e b * rationalCharacteristicPartial l z -
      e a * rationalCharacteristicPartial j z =
      e b * (rationalCharacteristicPartial l z -
        (rationalCharacteristicJacobian V i l / rationalCharacteristicJacobian V i j) *
          rationalCharacteristicPartial j z)
    rw [← hab]
    change e b * rationalCharacteristicPartial l z -
      e a * rationalCharacteristicPartial j z =
      e b * (rationalCharacteristicPartial l z -
        (e a / e b) * rationalCharacteristicPartial j z)
    field_simp [hbe]
  have hD (f : B K) : D' (e f) = e (D f) := by
    exact (rankOne_clearedPolynomialPartial_algebraMap a b j l f).symm
  apply rationalInvariant_reducedPair_dvd D D' hD p q hq hcop
  rw [hscale, rankOne_correctedPartial_velocityField_zero V i j l hp hm _ hz, mul_zero]

/-- At a specialization where the coefficient of the normal
derivative is nonzero, a vanishing polynomial solution and its
vanishing tangent derivative force its normal derivative to vanish.
This is the first-order propagation step for the noncharacteristic
line argument. -/
theorem rankOne_specialization_normalPartial_zero
    {F : Type*} [Field F] [Algebra K F]
    (φ : B K →ₐ[K] F) (a b p : B K) (j l : Fin 3)
    (hb : φ b ≠ 0)
    (hd : p ∣ rankOne_clearedPolynomialPartial a b j l p)
    (hp : φ p = 0) (hj : φ (pderiv j p) = 0) :
    φ (pderiv l p) = 0 := by
  obtain ⟨r, hr⟩ := hd
  change b * pderiv l p - a * pderiv j p = p * r at hr
  have h := congrArg φ hr
  change φ (b * pderiv l p - a * pderiv j p) = φ (p * r) at h
  simp only [map_sub, map_mul, hp, hj, mul_zero, zero_mul, sub_zero] at h
  exact (mul_eq_zero.mp h).resolve_left hb

end
end HC4.Polynomial.RankThreeCubic
