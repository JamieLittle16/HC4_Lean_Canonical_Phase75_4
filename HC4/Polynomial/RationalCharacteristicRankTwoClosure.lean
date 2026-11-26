module

public import HC4.Polynomial.RationalCharacteristicRankTwoConstantNormal

/-!
# Unconditional anchored rational characteristic rigidity

The only remaining rank-two branch has a constant normalized right
kernel. Its polynomial directional derivative of the source
potential has gradient proportional to the left normal.

A varying normalized normal would have a component t whose
differential is proportional to the normal itself. The straight
tangent e_j - t e_l kills both t and the polynomial directional
derivative. Differentiating the invariant polynomial line in
coordinate l and evaluating at the inverse of the nonzero
partial of t gives a contradiction.

Together with the verified variable-direction and rank-at-most-one
theorems this yields the original source adjugate annihilator,
with no rational rigidity premise.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

namespace RationalCharacteristicRankTwoClosure

abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev E (K : Type*) [Field K] := FractionRing (B K)
abbrev I := Unit ⊕ Fin 3
abbrev S (K : Type*) [Field K] := MvPolynomial I K

end RationalCharacteristicRankTwoClosure

open RationalCharacteristicRankTwoClosure (B E I S)

set_option maxHeartbeats 2000000 in
/-- The rational tangent to a normalized parameter component
acts by the difference of the two indicated coordinate partials. -/
theorem rankTwo_tangent_directional_apply
    (t : E K) (j l : Fin 3) (r : E K) :
    rankTwo_directionalDerivation
      (fun i => (if i = j then 1 else 0) -
        t * (if i = l then 1 else 0)) r =
      rationalCharacteristicPartial j r - t * rationalCharacteristicPartial l r := by
  classical
  rw [rankTwo_directionalDerivation_apply]
  simp only [sub_mul, Finset.sum_sub_distrib, mul_assoc, ← Finset.mul_sum]
  have h (m : Fin 3) :
      (∑ i : Fin 3, (if i = m then (1 : E K) else 0) *
        rationalCharacteristicPartial i r) = rationalCharacteristicPartial m r := by
    rw [Finset.sum_eq_single m]
    · simp
    · intro i _ hi
      simp [hi]
    · simp
  rw [h, h]

set_option maxHeartbeats 4000000 in
/-- A nonzero polynomial gradient cannot have a varying slope which
is itself constant along the associated tangent. The contradiction
takes place solely in the polynomial line parameter, not by
specializing any rational function at a pole. -/
theorem rankTwo_polynomial_tangent_impossible
    (g : B K) (t : E K) (j l : Fin 3)
    (hjl : j ≠ l)
    (ht : rationalCharacteristicPartial l t ≠ 0)
    (htj : rationalCharacteristicPartial j t =
      t * rationalCharacteristicPartial l t)
    (hg : algebraMap (B K) (E K) (pderiv l g) ≠ 0)
    (hgj : algebraMap (B K) (E K) (pderiv j g) =
      t * algebraMap (B K) (E K) (pderiv l g)) : False := by
  classical
  let z : Fin 3 → E K := fun i =>
    (if i = j then 1 else 0) - t * (if i = l then 1 else 0)
  let D := rankTwo_directionalDerivation z
  have hD (r : E K) : D r =
      rationalCharacteristicPartial j r - t * rationalCharacteristicPartial l r :=
    rankTwo_tangent_directional_apply t j l r
  have hDt : D t = 0 := by rw [hD, htj, sub_self]
  have hDz (i : Fin 3) : D (z i) = 0 := by
    by_cases hi : i = l
    · subst i
      have hlj : l ≠ j := Ne.symm hjl
      change D ((if l = j then 1 else 0) - t * (if l = l then 1 else 0)) = 0
      simp [hlj, hDt]
    · by_cases hi' : i = j <;> simp [z, hi, hi', hjl]
  have hDg : D (algebraMap (B K) (E K) g) = 0 := by
    rw [hD, rationalCharacteristicPartial_algebraMap,
      rationalCharacteristicPartial_algebraMap, hgj, sub_self]
  have hD2 : D (D (algebraMap (B K) (E K) g)) = 0 := by
    rw [hDg, map_zero]
  have hline : rankTwo_fibreEval z g =
      _root_.Polynomial.C (algebraMap (B K) (E K) g) := by
    have h := rankTwo_fibreEval_affine_of_second_zero z hDz g hD2
    rw [hDg, map_zero, mul_zero, add_zero] at h
    exact h
  have hpartial (i : Fin 3) : rationalCharacteristicPartial l (z i) =
      if i = l then -rationalCharacteristicPartial l t else 0 := by
    by_cases hi : i = l
    · subst i
      simp [z, Ne.symm hjl]
    · by_cases hi' : i = j <;> simp [z, hi, hi', hjl]
  have hchain := rankTwo_fibreEval_partial z g l
  rw [hline, coeffDeriv_C, rationalCharacteristicPartial_algebraMap] at hchain
  let r := (rationalCharacteristicPartial l t)⁻¹
  let ev := _root_.Polynomial.evalRingHom r
  have he := congrArg ev hchain
  change ev (_root_.Polynomial.C (algebraMap (B K) (E K) (pderiv l g))) =
      ev (∑ i : Fin 3, rankTwo_fibreEval z (pderiv i g) *
        (_root_.Polynomial.C (if i = l then 1 else 0) +
          _root_.Polynomial.X * _root_.Polynomial.C
            (rationalCharacteristicPartial l (z i)))) at he
  have hzero (i : Fin 3) :
      ev (_root_.Polynomial.C (if i = l then 1 else 0) +
        _root_.Polynomial.X * _root_.Polynomial.C
          (rationalCharacteristicPartial l (z i))) = 0 := by
    change (_root_.Polynomial.C (if i = l then 1 else 0) +
      _root_.Polynomial.X * _root_.Polynomial.C
        (rationalCharacteristicPartial l (z i))).eval r = 0
    rw [_root_.Polynomial.eval_add, _root_.Polynomial.eval_mul,
      _root_.Polynomial.eval_X, _root_.Polynomial.eval_C,
      _root_.Polynomial.eval_C, hpartial]
    by_cases hi : i = l
    · rw [if_pos hi, if_pos hi]
      change 1 + (rationalCharacteristicPartial l t)⁻¹ *
        (-rationalCharacteristicPartial l t) = 0
      rw [mul_neg, inv_mul_cancel₀ ht, add_neg_cancel]
    · rw [if_neg hi, if_neg hi, mul_zero, add_zero]
  rw [map_sum] at he
  simp only [map_mul, hzero, mul_zero, Finset.sum_const_zero] at he
  change (_root_.Polynomial.C (algebraMap (B K) (E K) (pderiv l g))).eval r = 0 at he
  rw [_root_.Polynomial.eval_C] at he
  exact hg he

set_option maxHeartbeats 4000000 in
/-- The last rank-two case: the normalized constant right kernel
and the genuine polynomial Hessian symmetrizer force a constant
left kernel of the actual velocity Jacobian. -/
theorem rankTwo_constantDirection_leftKernel
    (f : B K) (V : I → E K) (d : Fin 3 → K) (b : Fin 3 → E K)
    (k l : Fin 3)
    (hr : 2 ≤ (rationalCharacteristicJacobian V).rank)
    (h3 : rationalCharacteristicJacobian V ^ 3 = 0)
    (hk : d k = 1) (hl : b l = 1)
    (hw : rationalCharacteristicJacobian V *ᵥ
      (fun i => algebraMap K (E K) (d i)) = 0)
    (hb : b ᵥ* rationalCharacteristicJacobian V = 0)
    (hn : b ⬝ᵥ (fun i => algebraMap K (E K) (d i)) = 0)
    (hreg : ((hessian f).map (algebraMap (B K) (E K))).det ≠ 0)
    (hself : (rationalCharacteristicJacobian V).transpose *
      (hessian f).map (algebraMap (B K) (E K)) =
      (hessian f).map (algebraMap (B K) (E K)) *
        rationalCharacteristicJacobian V) :
    ∃ e : Fin 3 → K, e ≠ 0 ∧
      (fun i => algebraMap K (E K) (e i)) ᵥ* rationalCharacteristicJacobian V = 0 := by
  classical
  let w : Fin 3 → E K := fun i => algebraMap K (E K) (d i)
  let N := rationalCharacteristicJacobian V
  let H := (hessian f).map (algebraMap (B K) (E K))
  have hwk : w k = 1 := by
    change algebraMap K (E K) (d k) = 1
    rw [hk, map_one]
  have hw0 : w ≠ 0 := by
    intro h
    have he := congrFun h k
    rw [hwk] at he
    exact one_ne_zero he
  have hc (i j : Fin 3) : rationalCharacteristicPartial j (w i) = 0 :=
    Derivation.map_algebraMap _ _
  rcases rankTwo_constantDirection_normalDifferential V w b k l hr h3 hwk hl
    hw hb hn hc with hconst | hvar
  · have he (i : Fin 3) : ∃ e : K, b i = algebraMap K (E K) e :=
      rationalCharacteristicPartial_constants (b i) (hconst i)
    choose e he using he
    have he0 : e ≠ 0 := by
      intro hz
      have hh := he l
      rw [hl, hz, Pi.zero_apply, map_zero] at hh
      exact one_ne_zero hh
    refine ⟨e, he0, ?_⟩
    rw [show (fun i => algebraMap K (E K) (e i)) = b from
      funext (fun i => (he i).symm)]
    exact hb
  · obtain ⟨j, hj, hdiff⟩ := hvar
    have hjl : j ≠ l := by
      intro he
      subst j
      apply hj
      rw [hl, Derivation.map_one_eq_zero]
    obtain ⟨hz0, hzN⟩ := rankTwo_hessian_leftNormal H N hreg hself w hw0 hw
    let z := H *ᵥ w
    let c := z l
    have hprop (i : Fin 3) : z i = b i * c := by
      have he := rankTwo_leftKernel_minors_zero N hr b z hb hzN l i
      rw [hl, one_mul] at he
      exact he
    have hc0 : c ≠ 0 := by
      intro h
      apply hz0
      funext i
      change z i = 0
      rw [hprop, h, mul_zero]
    let g : B K := ∑ i : Fin 3, MvPolynomial.C (d i) * pderiv i f
    let e := algebraMap (B K) (E K)
    have hC (a : K) : e (MvPolynomial.C a) = algebraMap K (E K) a :=
      (IsScalarTower.toAlgHom K (B K) (E K)).commutes a
    have hg : e g = rankTwo_directionalDerivation w (e f) := by
      rw [rankTwo_directionalDerivation_apply]
      change e (∑ i : Fin 3, MvPolynomial.C (d i) * pderiv i f) = _
      have hpartial (i : Fin 3) : rationalCharacteristicPartial i (e f) =
          e (pderiv i f) := rationalCharacteristicPartial_algebraMap i f
      simp only [map_sum, map_mul, hC, hpartial, w]
    have hgdiff (i : Fin 3) : e (pderiv i g) = b i * c := by
      have he := rankTwo_fibreSlope_partial f w i
      change rationalCharacteristicPartial i (rankTwo_directionalDerivation w (e f)) =
        z i + ∑ j : Fin 3, e (pderiv j f) * rationalCharacteristicPartial i (w j) at he
      rw [← hg, rationalCharacteristicPartial_algebraMap] at he
      simp only [hc, mul_zero, Finset.sum_const_zero, add_zero] at he
      exact he.trans (hprop i)
    have hgl : e (pderiv l g) = c := by rw [hgdiff, hl, one_mul]
    exfalso
    apply rankTwo_polynomial_tangent_impossible g (b j) j l hjl hj (hdiff j)
    · change e (pderiv l g) ≠ 0
      rw [hgl]
      exact hc0
    · change e (pderiv j g) = b j * e (pderiv l g)
      rw [hgdiff, hgl]

set_option maxHeartbeats 3000000 in
/-- The original rank-two source always has a constant adjugate
annihilator, including both the constant and varying direction. -/
theorem rationalCharacteristic_rankTwo_adjugate_annihilator
    (a : K) (L : S K) (V : I → E K)
    (hdet : (hessian L).det = 0) (hV : V (.inl ()) = 1)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L)))
    (hm : ¬ ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    ∃ d : I → K, d ≠ 0 ∧
      (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
  classical
  rcases rankTwo_source_constantDirection_or_adjugate a L V hdet hV hreg hgrad hm with h | h
  · exact h
  · obtain ⟨d, b, k, l, c, hk, hl, _, hw, hb, hn, _⟩ := h
    have hr : 2 ≤ (rationalCharacteristicJacobian V).rank := by
      by_contra h
      apply hm
      intro a b i j
      by_contra hz
      exact h (rankTwo_rank_ge_two_of_minor _ a i b j hz)
    have h3 := rationalCharacteristicJacobian_cube_eq_zero a L V hV hreg
      (fun i => hgrad (.inr i))
    have hhreg := rationalCharacteristicHessian_det_ne_zero a L hreg
    rw [rationalCharacteristicHessian_eq_slice_hessian] at hhreg
    have hself := rationalCharacteristicJacobian_selfAdjoint a L V hV
      (fun i => hgrad (.inr i))
    change (rationalCharacteristicJacobian V).transpose *
        rationalCharacteristicHessian a L =
      rationalCharacteristicHessian a L * rationalCharacteristicJacobian V at hself
    rw [rationalCharacteristicHessian_eq_slice_hessian] at hself
    obtain ⟨b', hb0, hb'⟩ := rankTwo_constantDirection_leftKernel
      (referenceSlice a L) V d b k l hr h3 hk hl hw hb hn hhreg hself
    obtain ⟨e, he0, he⟩ := rationalCharacteristic_exists_annihilator_of_constant_leftKernel
      V hV b' hb0 hb'
    exact ⟨e, he0, rationalCharacteristic_adjugate_annihilator a L V e hdet hV hreg hgrad he⟩

/-- Full anchored rational characteristic rigidity. No rank,
transverse degree, pole or common parameter assumption remains. -/
theorem rationalCharacteristic_anchored_adjugate_annihilator
    (a : K) (L : S K)
    (hdet : (hessian L).det = 0)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0) :
    ∃ d : I → K, d ≠ 0 ∧
      (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
  classical
  obtain ⟨V, hV, hgrad, _⟩ :=
    exists_anchored_rationalCharacteristic_nilpotent a L hdet hreg
  by_cases hm : ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b
  · exact rationalCharacteristic_rankAtMostOne_adjugate_annihilator a L V hdet hV hreg hgrad hm
  · exact rationalCharacteristic_rankTwo_adjugate_annihilator a L V hdet hV hreg hgrad hm

end
end HC4.Polynomial.RankThreeCubic
