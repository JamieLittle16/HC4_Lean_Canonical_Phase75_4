import HC4.Polynomial.RationalCharacteristicRankTwoStraightFibre

/-!
# Polynomial rigidity along the straight velocity fibre

A straight direction w with H w = c b, b invariant and normalized,
has affine potential along its fibre. Its gradient displacement is
a scalar polynomial times b. Differentiating the affine potential
with respect to the original coordinates then forces the scalar
polynomial to be linear, and b to annihilate Dw.

The last cancellation uses evaluation at the root of a linear
polynomial, not a classification of congruences of lines.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

section Scalar

variable {F : Type*} [Field F]

/-- A nonzero affine slope, multiplied by a polynomial vanishing at
zero, cannot give a nonzero linear monomial unless the slope is
constant. The other components then have zero linear coefficient. -/
theorem rankTwo_gradient_scalarRigidity
    (R : _root_.Polynomial F) (b r : Fin 3 → F) (c : F) (k : Fin 3)
    (hb : b k = 1) (hc : c ≠ 0)
    (h : ∀ j, R * (_root_.Polynomial.C (b j) +
      _root_.Polynomial.X * _root_.Polynomial.C (r j)) =
        _root_.Polynomial.X * _root_.Polynomial.C (c * b j)) :
    R = _root_.Polynomial.X * _root_.Polynomial.C c ∧
      ∀ j, r j = 0 := by
  have hk := h k
  rw [hb, map_one, mul_one] at hk
  have hrk : r k = 0 := by
    by_contra hn
    have he := congrArg (_root_.Polynomial.eval (-(r k)⁻¹)) hk
    have hz : (-(r k)⁻¹) * r k = -1 := by
      rw [neg_mul, inv_mul_cancel₀ hn]
    simp only [_root_.Polynomial.eval_mul, _root_.Polynomial.eval_add,
      _root_.Polynomial.eval_one, _root_.Polynomial.eval_X,
      _root_.Polynomial.eval_C, hz, add_neg_cancel, mul_zero] at he
    exact (mul_ne_zero (neg_ne_zero.mpr (inv_ne_zero hn)) hc) he.symm
  have hR : R = _root_.Polynomial.X * _root_.Polynomial.C c := by
    simpa [hrk] using hk
  refine ⟨hR, ?_⟩
  intro j
  have he := h j
  rw [hR] at he
  have hC : (_root_.Polynomial.C c : _root_.Polynomial F) ≠ 0 :=
    _root_.Polynomial.C_ne_zero.mpr hc
  have hx : (_root_.Polynomial.X : _root_.Polynomial F) ≠ 0 :=
    _root_.Polynomial.X_ne_zero
  have hp : (_root_.Polynomial.X * _root_.Polynomial.C c) *
      (_root_.Polynomial.X * _root_.Polynomial.C (r j)) = 0 := by
    have he' : (_root_.Polynomial.X * _root_.Polynomial.C c) *
        _root_.Polynomial.C (b j) = _root_.Polynomial.X * _root_.Polynomial.C (c * b j) := by
      rw [map_mul, mul_assoc]
    rw [mul_add, he'] at he
    exact add_left_cancel (he.trans (add_zero _).symm)
  have hz := (mul_eq_zero.mp hp).resolve_left (mul_ne_zero hx hC)
  exact _root_.Polynomial.C_eq_zero.mp ((mul_eq_zero.mp hz).resolve_left hx)

end Scalar

variable {K : Type*} [Field K] [CharZero K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev I := Unit ⊕ Fin 3
private abbrev S (K : Type*) [Field K] := MvPolynomial I K

def rankTwo_fibreEval (w : Fin 3 → E K) :
    B K →ₐ[K] _root_.Polynomial (E K) :=
  lineEval (fun i => algebraMap (B K) (E K) (X i)) w

theorem rankTwo_fibreEval_coeff_zero (w : Fin 3 → E K) (p : B K) :
    (rankTwo_fibreEval w p).coeff 0 = algebraMap (B K) (E K) p := by
  rw [rankTwo_fibreEval, cubic_lineEval_coeff_zero]
  let g := IsScalarTower.toAlgHom K (B K) (E K)
  have he : MvPolynomial.aeval (fun i : Fin 3 => algebraMap (B K) (E K) (X i)) = g := by
    ext i
    exact MvPolynomial.aeval_X _ i
  exact AlgHom.congr_fun he p

/-- Differentiate a polynomial line substitution in an original
coordinate (rather than along the fibre). -/
theorem rankTwo_fibreEval_partial
    (w : Fin 3 → E K) (p : B K) (j : Fin 3) :
    coeffDeriv (rationalCharacteristicPartial j) (rankTwo_fibreEval w p) =
      ∑ i : Fin 3, rankTwo_fibreEval w (pderiv i p) *
        (_root_.Polynomial.C (if i = j then 1 else 0) +
          _root_.Polynomial.X * _root_.Polynomial.C (rationalCharacteristicPartial j (w i))) := by
  classical
  let z : Fin 3 → _root_.Polynomial (E K) := fun i =>
    _root_.Polynomial.C (algebraMap (B K) (E K) (X i)) +
      _root_.Polynomial.C (w i) * _root_.Polynomial.X
  have he : rankTwo_fibreEval w = MvPolynomial.aeval z := rfl
  have hz (i : Fin 3) :
      rationalCharacteristicPartial j (algebraMap (B K) (E K) (X i)) =
        if i = j then 1 else 0 := by
    rw [rationalCharacteristicPartial_algebraMap]
    by_cases h : i = j
    · subst i; simp
    · simp [h, pderiv_X_of_ne h]
  have hd (i : Fin 3) : coeffDeriv (rationalCharacteristicPartial j) (z i) =
      _root_.Polynomial.C (if i = j then 1 else 0) +
        _root_.Polynomial.X * _root_.Polynomial.C (rationalCharacteristicPartial j (w i)) := by
    simp only [z, map_add, coeffDeriv_C, Derivation.leibniz, smul_eq_mul,
      coeffDeriv_X, mul_zero, zero_add, hz]
  rw [he, derivation_aeval]
  simp only [hd]

/-- A polynomial whose directional derivative is constant along a
straight fibre restricts to an affine polynomial on that fibre. -/
theorem rankTwo_fibreEval_affine_of_second_zero
    (w : Fin 3 → E K)
    (hw : ∀ i, rankTwo_directionalDerivation w (w i) = 0)
    (p : B K)
    (h : rankTwo_directionalDerivation w
      (rankTwo_directionalDerivation w (algebraMap (B K) (E K) p)) = 0) :
    rankTwo_fibreEval w p =
      _root_.Polynomial.C (algebraMap (B K) (E K) p) +
        _root_.Polynomial.X * _root_.Polynomial.C
          (rankTwo_directionalDerivation w (algebraMap (B K) (E K) p)) := by
  let D := rankTwo_directionalDerivation w
  let e := rankTwo_fibreEval w
  let g := algebraMap (B K) (E K)
  have ht : coeffDeriv D (e p) = _root_.Polynomial.derivative (e p) :=
    rankTwo_lineEval_coeffDeriv_eq_derivative w hw p
  change e p = _root_.Polynomial.C (g p) + _root_.Polynomial.X * _root_.Polynomial.C (D (g p))
  apply sub_eq_zero.mp
  apply rankTwo_transportPolynomial_eq_zero D
  · have h' : D (D (g p)) = 0 := h
    simp only [map_sub, map_add, Derivation.leibniz, smul_eq_mul,
      coeffDeriv_C, coeffDeriv_X, h', map_zero, mul_zero, add_zero,
      zero_add, ht, _root_.Polynomial.derivative_C,
      _root_.Polynomial.derivative_mul, _root_.Polynomial.derivative_X, one_mul]
  · simp only [_root_.Polynomial.coeff_sub, _root_.Polynomial.coeff_add,
      _root_.Polynomial.coeff_C_zero, _root_.Polynomial.coeff_X_mul_zero,
      add_zero, e, rankTwo_fibreEval_coeff_zero, sub_self, g]

/-- All gradient displacements lie in the invariant normal line,
by uniqueness of the coefficient-transport recurrence. -/
theorem rankTwo_fibreEval_gradient_normal
    (f : B K) (w b : Fin 3 → E K) (c : E K) (k : Fin 3)
    (hw : ∀ i, rankTwo_directionalDerivation w (w i) = 0)
    (hb : ∀ i, rankTwo_directionalDerivation w (b i) = 0)
    (hk : b k = 1)
    (hh : (hessian f).map (algebraMap (B K) (E K)) *ᵥ w = c • b) :
    let R := rankTwo_fibreEval w (pderiv k f) -
      _root_.Polynomial.C (algebraMap (B K) (E K) (pderiv k f))
    ∀ i, rankTwo_fibreEval w (pderiv i f) -
      _root_.Polynomial.C (algebraMap (B K) (E K) (pderiv i f)) =
        R * _root_.Polynomial.C (b i) := by
  let D := rankTwo_directionalDerivation w
  let g := algebraMap (B K) (E K)
  let e := rankTwo_fibreEval w
  let Q (i : Fin 3) := e (pderiv i f) - _root_.Polynomial.C (g (pderiv i f))
  have hg (i : Fin 3) : D (g (pderiv i f)) = c * b i := by
    rw [show D (g (pderiv i f)) =
      ((hessian f).map g *ᵥ w) i from rankTwo_referenceGradient_derivative f w i, hh]
    rfl
  have hQ (i : Fin 3) : coeffDeriv D (Q i) =
      _root_.Polynomial.derivative (Q i) - _root_.Polynomial.C (c * b i) := by
    have ht : coeffDeriv D (e (pderiv i f)) =
        _root_.Polynomial.derivative (e (pderiv i f)) :=
      rankTwo_lineEval_coeffDeriv_eq_derivative w hw _
    simp only [Q, map_sub, coeffDeriv_C, hg, ht, sub_zero,
      _root_.Polynomial.derivative_C]
  have hQ0 (i : Fin 3) : (Q i).coeff 0 = 0 := by
    simp only [Q, _root_.Polynomial.coeff_sub, _root_.Polynomial.coeff_C_zero,
      e, rankTwo_fibreEval_coeff_zero, g, sub_self]
  change ∀ i : Fin 3, Q i = Q k * _root_.Polynomial.C (b i)
  intro i
  apply sub_eq_zero.mp
  apply rankTwo_transportPolynomial_eq_zero D
  · have hb' : D (b i) = 0 := hb i
    have hki := hQ k
    rw [hk, mul_one] at hki
    simp only [map_sub, Derivation.leibniz, smul_eq_mul, coeffDeriv_C, hb',
      map_zero, mul_zero, zero_add, hQ i, hki, map_mul,
      _root_.Polynomial.derivative_mul, _root_.Polynomial.derivative_C,
      add_zero]
    ring
  · rw [_root_.Polynomial.coeff_sub, mul_comm (Q k), _root_.Polynomial.coeff_C_mul,
      hQ0, hQ0, mul_zero, sub_self]

/-- Differentiate the potential's slope. Its differential is
the sum of the Hessian-direction product and the gradient paired
with the derivative of the direction. -/
theorem rankTwo_fibreSlope_partial
    (f : B K) (w : Fin 3 → E K) (j : Fin 3) :
    rationalCharacteristicPartial j
      (rankTwo_directionalDerivation w (algebraMap (B K) (E K) f)) =
      ((hessian f).map (algebraMap (B K) (E K)) *ᵥ w) j +
        ∑ i : Fin 3, algebraMap (B K) (E K) (pderiv i f) *
          rationalCharacteristicPartial j (w i) := by
  rw [rankTwo_directionalDerivation_apply]
  simp only [rationalCharacteristicPartial_algebraMap, map_sum,
    Derivation.leibniz, smul_eq_mul, Finset.sum_add_distrib]
  congr 1
  change (∑ i : Fin 3, w i * algebraMap (B K) (E K) (pderiv j (pderiv i f))) =
    ∑ i : Fin 3, algebraMap (B K) (E K) (pderiv i (pderiv j f)) * w i
  apply Finset.sum_congr rfl
  intro i _
  rw [HC4.Newton.pderiv_comm_backport j i, mul_comm]


set_option maxHeartbeats 2000000 in
/-- Polynomiality forces exact affine gradient transport and makes the
left normal annihilate the full derivative of the straight direction. -/
theorem rankTwo_fibre_affineGradient
    (f : B K) (w b : Fin 3 → E K) (c : E K) (k : Fin 3)
    (hw : ∀ i, rankTwo_directionalDerivation w (w i) = 0)
    (hb : ∀ i, rankTwo_directionalDerivation w (b i) = 0)
    (hk : b k = 1) (hc : c ≠ 0)
    (hn : b ⬝ᵥ w = 0)
    (hh : (hessian f).map (algebraMap (B K) (E K)) *ᵥ w = c • b) :
    (∀ i, rankTwo_fibreEval w (pderiv i f) =
      _root_.Polynomial.C (algebraMap (B K) (E K) (pderiv i f)) +
        _root_.Polynomial.X * _root_.Polynomial.C (c * b i)) ∧
    (∀ j, (∑ i : Fin 3, b i * rationalCharacteristicPartial j (w i)) = 0) := by
  classical
  let D := rankTwo_directionalDerivation w
  let g := algebraMap (B K) (E K)
  let e := rankTwo_fibreEval w
  let R := e (pderiv k f) - _root_.Polynomial.C (g (pderiv k f))
  let C := _root_.Polynomial.C (R := E K)
  let t : _root_.Polynomial (E K) := _root_.Polynomial.X
  have hrow (i : Fin 3) : ((hessian f).map g *ᵥ w) i = c * b i :=
    congrFun hh i
  have hg (i : Fin 3) : D (g (pderiv i f)) = c * b i :=
    (rankTwo_referenceGradient_derivative f w i).trans (hrow i)
  have hsum : D (g f) = ∑ i : Fin 3, w i * g (pderiv i f) := by
    rw [show D (g f) = ∑ i : Fin 3, w i * rationalCharacteristicPartial i (g f)
      from rankTwo_directionalDerivation_apply w (g f)]
    simp only [g, rationalCharacteristicPartial_algebraMap]
  have hf2 : D (D (g f)) = 0 := by
    rw [hsum, map_sum]
    have hw' (i : Fin 3) : D (w i) = 0 := hw i
    simp only [Derivation.leibniz, smul_eq_mul, hg, hw', mul_zero, add_zero]
    have hfactor : (∑ i : Fin 3, w i * (c * b i)) = c * (b ⬝ᵥ w) := by
      rw [dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [hfactor, hn, mul_zero]
  have hf : e f = C (g f) + t * C (D (g f)) :=
    rankTwo_fibreEval_affine_of_second_zero w hw f hf2
  have hnormal (i : Fin 3) : e (pderiv i f) = C (g (pderiv i f)) + R * C (b i) := by
    have h := rankTwo_fibreEval_gradient_normal f w b c k hw hb hk hh i
    change e (pderiv i f) - C (g (pderiv i f)) = R * C (b i) at h
    linear_combination h
  have hcontract (j : Fin 3) :
      R * (C (b j) + t * C (∑ i : Fin 3, b i * rationalCharacteristicPartial j (w i))) =
        t * C (c * b j) := by
    let d := rationalCharacteristicPartial (K := K) j
    let r : Fin 3 → E K := fun i => d (w i)
    have hchain : coeffDeriv d (e f) =
        e (pderiv j f) + t * ∑ i : Fin 3, e (pderiv i f) * C (r i) := by
      have h := rankTwo_fibreEval_partial w f j
      change coeffDeriv d (e f) = ∑ i : Fin 3, e (pderiv i f) *
        (C (if i = j then 1 else 0) + t * C (r i)) at h
      rw [h]
      simp only [mul_add, Finset.sum_add_distrib]
      have hz : (∑ i : Fin 3, e (pderiv i f) * C (if i = j then 1 else 0)) =
          e (pderiv j f) := by
        rw [Finset.sum_eq_single j]
        · simp [C]
        · intro i _ hi
          simp [C, hi]
        · simp
      rw [hz]
      congr 1
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    have hdiff : d (D (g f)) = c * b j + ∑ i : Fin 3, g (pderiv i f) * r i := by
      have h := rankTwo_fibreSlope_partial f w j
      change d (D (g f)) = ((hessian f).map g *ᵥ w) j +
        ∑ i : Fin 3, g (pderiv i f) * r i at h
      rw [h, hrow]
    have hdf : d (g f) = g (pderiv j f) :=
      rationalCharacteristicPartial_algebraMap j f
    have heq : coeffDeriv d (e f) =
        C (g (pderiv j f)) +
          t * (C (c * b j) + ∑ i : Fin 3, C (g (pderiv i f)) * C (r i)) := by
      rw [hf]
      change coeffDeriv d (_root_.Polynomial.C (g f) +
        _root_.Polynomial.X * _root_.Polynomial.C (D (g f))) = _
      simp only [map_add, Derivation.leibniz, smul_eq_mul, coeffDeriv_C,
        coeffDeriv_X, hdf, hdiff, mul_zero, add_zero, map_sum, map_mul]
      rfl
    have hsum' : (∑ i : Fin 3, e (pderiv i f) * C (r i)) =
        (∑ i : Fin 3, C (g (pderiv i f)) * C (r i)) +
          R * C (∑ i : Fin 3, b i * r i) := by
      simp only [hnormal, add_mul, Finset.sum_add_distrib]
      congr 1
      rw [map_sum, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      rw [map_mul, mul_assoc]
    rw [hchain, hnormal j, hsum'] at heq
    change R * (C (b j) + t * C (∑ i : Fin 3, b i * r i)) = t * C (c * b j)
    linear_combination heq
  obtain ⟨hR, hr⟩ := rankTwo_gradient_scalarRigidity R b
    (fun j => ∑ i : Fin 3, b i * rationalCharacteristicPartial j (w i)) c k hk hc hcontract
  refine ⟨?_, hr⟩
  intro i
  change e (pderiv i f) = C (g (pderiv i f)) + t * C (c * b i)
  rw [hnormal, hR, map_mul, mul_assoc]


set_option maxHeartbeats 2000000 in
/-- The two earlier source directions span the same kernel. Combining
their normalizations supplies all the affine-gradient hypotheses from
the anchored source itself, with no new geometric assumption. -/
theorem rankTwo_source_affineGradient
    (a : K) (L : S K) (V : I → E K)
    (hV : V (.inl ()) = 1)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L)))
    (hm : ¬ ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    ∃ (w b : Fin 3 → E K) (k l : Fin 3) (c : E K),
      w k = 1 ∧ b l = 1 ∧ c ≠ 0 ∧
      rationalCharacteristicJacobian V *ᵥ w = 0 ∧
      b ᵥ* rationalCharacteristicJacobian V = 0 ∧
      b ⬝ᵥ w = 0 ∧
      (∀ i, rankTwo_directionalDerivation w (w i) = 0) ∧
      (∀ i, rankTwo_directionalDerivation w (b i) = 0) ∧
      (∀ i, rankTwo_fibreEval w (pderiv i (referenceSlice a L)) =
        _root_.Polynomial.C (algebraMap (B K) (E K) (pderiv i (referenceSlice a L))) +
          _root_.Polynomial.X * _root_.Polynomial.C (c * b i)) ∧
      (∀ j, (∑ i : Fin 3, b i * rationalCharacteristicPartial j (w i)) = 0) := by
  classical
  let N := rationalCharacteristicJacobian V
  let H := rationalCharacteristicHessian a L
  obtain ⟨w, k, hk, hw, hww, _⟩ := rankTwo_source_straightDirection a L V hV hreg hgrad hm
  obtain ⟨u, b, l, hl, hu, hH, hb, hn, _, _⟩ :=
    rankTwo_exists_normalizedDualDirection a L V hV hreg hgrad hm
  have hr : 2 ≤ N.rank := by
    by_contra h
    apply hm
    intro a b i j
    by_contra hz
    exact h (rankTwo_rank_ge_two_of_minor N a i b j hz)
  have hprop : u = u k • w := by
    funext i
    have he := rankTwo_rightKernel_minors_zero N hr w u hw hu k i
    rw [hk, one_mul] at he
    change u i = u k * w i
    rw [he, mul_comm]
  have huk : u k ≠ 0 := by
    intro hz
    have he : u = 0 := by rw [hprop, hz, zero_smul]
    have hb0 : b = 0 := by rw [← hH, he, Matrix.mulVec_zero]
    have he' := congrFun hb0 l
    rw [hl] at he'
    exact one_ne_zero he'
  let c := (u k)⁻¹
  have hwprop : w = c • u := by
    funext i
    change w i = (u k)⁻¹ * u i
    have he : u i = u k * w i := congrFun hprop i
    rw [he, ← mul_assoc, inv_mul_cancel₀ huk, one_mul]
  have hh : H *ᵥ w = c • b := by
    rw [hwprop, Matrix.mulVec_smul, hH]
  have hn' : b ⬝ᵥ w = 0 := by
    rw [hwprop]
    change (∑ i : Fin 3, b i * (c * u i)) = 0
    have he : (∑ i : Fin 3, b i * (c * u i)) = c * (b ⬝ᵥ u) := by
      rw [dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      ring
    rw [he, hn, mul_zero]
  have hbb := rankTwo_normalizedLeftNormal_invariant V w b hr hw hb l hl
  change rationalCharacteristicHessian a L *ᵥ w = c • b at hh
  rw [rationalCharacteristicHessian_eq_slice_hessian] at hh
  obtain ⟨hg, hdw⟩ := rankTwo_fibre_affineGradient (referenceSlice a L) w b c l
    hww hbb hl (inv_ne_zero huk) hn' hh
  exact ⟨w, b, k, l, c, hk, hl, inv_ne_zero huk, hw, hb, hn', hww, hbb, hg, hdw⟩

end
end HC4.Polynomial.RankThreeCubic
