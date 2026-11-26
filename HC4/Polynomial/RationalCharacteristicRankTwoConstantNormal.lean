module

public import HC4.Polynomial.RationalCharacteristicRankTwoVariableClosure

/-!
# Normal integrability with a constant right kernel

When the normalized right kernel is ground-field constant, the
derivative of the normalized left normal has two independent
constant covectors in its left kernel. Its minors therefore vanish.
A nonzero derivative pivot yields a parameter which is an actual
component of the normal itself.

Differentiated integrability makes beta * N proportional to dt.
Since beta annihilates the constant right kernel, nilpotence makes
this row a left kernel of N. It is nonzero, so dt is proportional
to the normalized source normal.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

namespace RationalCharacteristicRankTwoConstantNormal

abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev E (K : Type*) [Field K] := FractionRing (B K)
abbrev I := Unit ⊕ Fin 3

end RationalCharacteristicRankTwoConstantNormal

open RationalCharacteristicRankTwoConstantNormal (B E I)

set_option maxHeartbeats 3000000 in
/-- For a constant normalized right kernel, a nonconstant component
of the normalized left normal has differential in the left kernel.
The component has a nonzero derivative in the normal's pivot
coordinate itself. -/
theorem rankTwo_constantDirection_normalDifferential
    (V : I → E K) (w b : Fin 3 → E K) (k l : Fin 3)
    (hr : 2 ≤ (rationalCharacteristicJacobian V).rank)
    (h3 : rationalCharacteristicJacobian V ^ 3 = 0)
    (hk : w k = 1) (hl : b l = 1)
    (hw : rationalCharacteristicJacobian V *ᵥ w = 0)
    (hb : b ᵥ* rationalCharacteristicJacobian V = 0)
    (hn : b ⬝ᵥ w = 0)
    (hc : ∀ i j, rationalCharacteristicPartial j (w i) = 0) :
    (∀ i j, rationalCharacteristicPartial j (b i) = 0) ∨
      ∃ j : Fin 3, rationalCharacteristicPartial l (b j) ≠ 0 ∧
        ∀ i, rationalCharacteristicPartial i (b j) =
          b i * rationalCharacteristicPartial l (b j) := by
  classical
  let N := rationalCharacteristicJacobian V
  let A := rationalCharacteristicJacobian (rankTwo_directionLift b)
  have hwb : w ⬝ᵥ b = 0 := by
    change (∑ i : Fin 3, w i * b i) = 0
    simpa only [dotProduct, mul_comm] using hn
  have hrow : ∀ j, (∑ i : Fin 3, w i * rationalCharacteristicPartial j (b i)) = 0 := by
    intro j
    have h := rankTwo_derivation_dot (rationalCharacteristicPartial (K := K) j) w b
    rw [hwb, map_zero] at h
    change (0 : E K) = (∑ i : Fin 3, w i * rationalCharacteristicPartial j (b i)) +
      ∑ i : Fin 3, rationalCharacteristicPartial j (w i) * b i at h
    simpa only [hc, zero_mul, Finset.sum_const_zero, add_zero] using h.symm
  have hm := rankTwo_directionJacobian_minors b w l k hl hk hwb hrow
  by_cases hz : ∀ i j, rationalCharacteristicPartial j (b i) = 0
  · exact Or.inl hz
  · right
    push_neg at hz
    obtain ⟨j, p, hp⟩ := hz
    let t := b j
    let dt : Fin 3 → E K := fun i => rationalCharacteristicPartial i t
    let beta : Fin 3 → E K := fun i => rationalCharacteristicPartial p (b i) / dt p
    have hp' : dt p ≠ 0 := hp
    have hdb (i m : Fin 3) : rationalCharacteristicPartial m (b i) = dt m * beta i := by
      have he := hm i j m p
      change rationalCharacteristicPartial m (b i) * dt p =
        rationalCharacteristicPartial p (b i) * dt m at he
      apply (mul_right_cancel₀ hp')
      calc
        rationalCharacteristicPartial m (b i) * dt p =
            rationalCharacteristicPartial p (b i) * dt m := he
        _ = (dt m * beta i) * dt p := by
          change rationalCharacteristicPartial p (b i) * dt m =
            (dt m * (rationalCharacteristicPartial p (b i) / dt p)) * dt p
          rw [mul_assoc, div_mul_cancel₀ _ hp', mul_comm]
    have hbl : beta l = 0 := by
      change rationalCharacteristicPartial p (b l) / dt p = 0
      rw [hl, Derivation.map_one_eq_zero, zero_div]
    have hbj : beta j = 1 := div_self hp'
    have hbw : beta ⬝ᵥ w = 0 := by
      have he := hrow p
      have hf : (∑ i : Fin 3, w i * rationalCharacteristicPartial p (b i)) =
          dt p * (beta ⬝ᵥ w) := by
        rw [dotProduct, Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro i _
        rw [hdb i p]
        ring
      rw [hf] at he
      exact (mul_eq_zero.mp he).resolve_left hp'
    let R := beta ᵥ* N
    have hR (m : Fin 3) : R m = dt m * (R p / dt p) := by
      have he := rankTwo_normalDerivative_row_minors V b beta t hb hdb m p
      change dt p * R m = dt m * R p at he
      apply (mul_left_cancel₀ hp')
      calc
        dt p * R m = dt m * R p := he
        _ = dt p * (dt m * (R p / dt p)) := by
          calc
            dt m * R p = dt m * ((R p / dt p) * dt p) := by
              rw [div_mul_cancel₀ _ hp']
            _ = _ := by ring
    have hRp : R p ≠ 0 := by
      intro hz
      have hRN : beta ᵥ* N = 0 := by
        funext m
        change R m = 0
        rw [hR, hz, zero_div, mul_zero]
      have he := rankTwo_leftKernel_minors_zero N hr b beta hb hRN l j
      rw [hl, hbj, hbl, one_mul, mul_zero] at he
      exact one_ne_zero he
    have hRN : R ᵥ* N = 0 := by
      funext m
      let u : Fin 3 → E K := fun i => N i m
      have hu : b ⬝ᵥ u = 0 := congrFun hb m
      exact rankTwo_normalPlane_image_pair_zero N w b u beta k l hr h3 hk hl hw hb hu hbw
    have hprop (m : Fin 3) : R m = b m * R l := by
      have he := rankTwo_leftKernel_minors_zero N hr b R hb hRN l m
      rw [hl, one_mul] at he
      exact he
    have hdl : dt l ≠ 0 := by
      intro hz
      have h1 := hR l
      rw [hz, zero_mul] at h1
      apply hRp
      rw [hprop p, h1, mul_zero]
    refine ⟨j, hdl, ?_⟩
    intro m
    change dt m = b m * dt l
    apply (mul_right_cancel₀ (div_ne_zero hRp hp'))
    calc
      dt m * (R p / dt p) = R m := (hR m).symm
      _ = b m * R l := hprop m
      _ = (b m * dt l) * (R p / dt p) := by
        rw [hR l, mul_assoc]

end
end HC4.Polynomial.RankThreeCubic
