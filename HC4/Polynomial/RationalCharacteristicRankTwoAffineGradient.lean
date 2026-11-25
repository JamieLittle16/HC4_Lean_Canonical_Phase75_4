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
    rw [mul_comm (_root_.Polynomial.C (rationalCharacteristicPartial j (w i))) _root_.Polynomial.X]
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
      coeffDeriv_C, coeffDeriv_X, h', map_zero, mul_zero, zero_mul, add_zero,
      zero_add, ht, _root_.Polynomial.derivative_add, _root_.Polynomial.derivative_C,
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
  intro i
  change Q i = Q k * _root_.Polynomial.C (b i)
  apply sub_eq_zero.mp
  apply rankTwo_transportPolynomial_eq_zero D
  · have hb' : D (b i) = 0 := hb i
    have hki := hQ k
    rw [hk, mul_one] at hki
    simp only [map_sub, Derivation.leibniz, smul_eq_mul, coeffDeriv_C, hb',
      map_zero, mul_zero, zero_add, hQ i, hki, sub_mul, ← map_mul,
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

end
end HC4.Polynomial.RankThreeCubic
