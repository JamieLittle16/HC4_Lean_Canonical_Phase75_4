module

public import HC4.Polynomial.RationalCharacteristicRankTwoDirectionParameter

/-!
# The nonconstant direction parameter is affine or already rigid

Clear a common denominator from the parametrized direction.
Its invariance of the parameter is exactly the evaluated trace
identity used in the earlier rank-one proof, with the direction
itself in place of the derivative vector. If the direction
polynomials have independent components, the verified trace
lift and symmetric pencil rigidity make the reduced numerator
and denominator affine.

Otherwise a constant normal annihilates the direction and its
derivative. These span the actual normal plane, so it also
annihilates the original velocity Jacobian.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

section Algebra

variable {F : Type*} [Field F]

/-- Two covectors annihilating the direction and its nonzero
tangent are proportional when the normalized direction coordinate
is one and the tangent coordinate is zero. -/
theorem rankTwo_direction_normal_proportional
    (w u b d : Fin 3 → F) (k l i : Fin 3)
    (hw : w k = 1) (hu : u k = 0) (hui : u i ≠ 0)
    (hb : b l = 1)
    (hbw : b ⬝ᵥ w = 0) (hbu : b ⬝ᵥ u = 0)
    (hdw : d ⬝ᵥ w = 0) (hdu : d ⬝ᵥ u = 0) :
    ∀ j : Fin 3, d j = b j * d l := by
  classical
  let A : Matrix (Fin 3) (Fin 3) F := fun i j => ![w i, u i, 0] j
  have hminor : A k 0 * A i 1 ≠ A k 1 * A i 0 := by
    change w k * u i ≠ u k * w i
    rw [hw, hu, one_mul, zero_mul]
    exact hui
  have hr := rankTwo_rank_ge_two_of_minor A k i 0 1 hminor
  have hbA : b ᵥ* A = 0 := by
    funext j
    fin_cases j
    · exact hbw
    · exact hbu
    · change (∑ i : Fin 3, b i * 0) = 0
      simp
  have hdA : d ᵥ* A = 0 := by
    funext j
    fin_cases j
    · exact hdw
    · exact hdu
    · change (∑ i : Fin 3, d i * 0) = 0
      simp
  intro j
  have h := rankTwo_leftKernel_minors_zero A hr b d hbA hdA l j
  rw [hb, one_mul] at h
  exact h

end Algebra

variable {K : Type*} [Field K] [CharZero K]

namespace RationalCharacteristicRankTwoAffineParameter

abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev E (K : Type*) [Field K] := FractionRing (B K)
abbrev I := Unit ⊕ Fin 3
abbrev S (K : Type*) [Field K] := MvPolynomial I K
abbrev P (K : Type*) [Field K] := _root_.Polynomial K

end RationalCharacteristicRankTwoAffineParameter

open RationalCharacteristicRankTwoAffineParameter (B E I S P)

/-- Clear a common nonzero denominator from the direction components,
not from their derivatives. -/
theorem rankTwo_direction_polynomialVector
    (w : Fin 3 → E K) (t : E K) (A Q : Fin 3 → P K)
    (hq : ∀ i, (Q i).eval₂ (algebraMap K (E K)) t ≠ 0)
    (hw : ∀ i, w i = (A i).eval₂ (algebraMap K (E K)) t /
      (Q i).eval₂ (algebraMap K (E K)) t) :
    ∃ (W : Fin 3 → P K) (s : E K), s ≠ 0 ∧
      ∀ i, (W i).eval₂ (algebraMap K (E K)) t = s * w i := by
  classical
  let ev : P K →+* E K := _root_.Polynomial.eval₂RingHom (algebraMap K (E K)) t
  let R (i : Fin 3) : P K := ∏ j ∈ Finset.univ.erase i, Q j
  let L : P K := ∏ j : Fin 3, Q j
  have hL (i : Fin 3) : L = Q i * R i :=
    (Finset.mul_prod_erase _ _ (Finset.mem_univ i)).symm
  have hs : ev L ≠ 0 := by
    change ev (∏ j : Fin 3, Q j) ≠ 0
    rw [map_prod]
    exact Finset.prod_ne_zero_iff.mpr (fun j _ => hq j)
  refine ⟨fun i => A i * R i, ev L, hs, ?_⟩
  intro i
  change ev (A i * R i) = ev L * w i
  have hi : w i = ev (A i) / ev (Q i) := hw i
  rw [hi, hL i, map_mul, map_mul]
  have hqi : ev (Q i) ≠ 0 := hq i
  field_simp [hqi]

/-- The evaluated directional trace identity lifts for any invariant
parameter, whether or not the direction is itself a velocity. -/
theorem rankTwo_direction_trace_lift
    (w : Fin 3 → E K) (t : E K) (W : Fin 3 → P K) (s : E K)
    (_hs : s ≠ 0)
    (hW : ∀ i, (W i).eval₂ (algebraMap K (E K)) t = s * w i)
    (ht : rankTwo_directionalDerivation w t = 0)
    (p q : B K) (hq : q ≠ 0) (hcop : IsRelPrime p q)
    (hpos : 0 < max p.totalDegree q.totalDegree)
    (hrep : algebraMap (B K) (E K) p / algebraMap (B K) (E K) q = t) :
    rankOne_tracePolynomial p W =
      _root_.Polynomial.X * rankOne_tracePolynomial q W := by
  let g := algebraMap (B K) (E K)
  have heval (f : B K) :
      (rankOne_tracePolynomial f W).eval₂ g t =
        ∑ j : Fin 3, g (pderiv j f) * (s * w j) := by
    unfold rankOne_tracePolynomial
    rw [_root_.Polynomial.eval₂_finset_sum]
    apply Finset.sum_congr rfl
    intro j _
    rw [_root_.Polynomial.eval₂_mul, _root_.Polynomial.eval₂_C,
      rankOne_parameter_eval_map, hW]
  have hd (j : Fin 3) : rationalCharacteristicPartial j t * g q =
      g (pderiv j p) - t * g (pderiv j q) := by
    rw [← hrep]
    exact rationalParameter_cleared_partial p q hq j
  have hz : (∑ j : Fin 3, g (pderiv j p) * (s * w j)) -
      t * (∑ j : Fin 3, g (pderiv j q) * (s * w j)) = 0 := by
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    have he : (∑ j : Fin 3, (g (pderiv j p) * (s * w j) -
        t * (g (pderiv j q) * (s * w j)))) =
        (s * g q) * rankTwo_directionalDerivation w t := by
      rw [rankTwo_directionalDerivation_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      calc
        _ = (s * w j) * (g (pderiv j p) - t * g (pderiv j q)) := by ring
        _ = _ := by rw [← hd j]; ring
    rw [he, ht, mul_zero]
  apply rankOne_lifted_trace_of_evaluated_trace p q W hq hcop hpos
  rw [hrep, heval, heval]
  exact sub_eq_zero.mp hz

/-- If the direction has a nonzero constant orthogonal covector,
then the same covector annihilates the original velocity Jacobian.
Differentiate the constant relation on the direction and use the
nonzero parameter derivative to annihilate its tangent. -/
theorem rankTwo_direction_constantNormal_transfer
    (V : I → E K) (w b : Fin 3 → E K) (k l : Fin 3)
    (hk : w k = 1) (hl : b l = 1)
    (hn : b ⬝ᵥ w = 0) (hb : b ᵥ* rationalCharacteristicJacobian V = 0)
    (t : E K) (u : Fin 3 → E K) (s : E K) (hs : s ≠ 0)
    (hfac : ∀ i j, rationalCharacteristicPartial j (w i) =
      s * u i * rationalCharacteristicPartial j t)
    (hi : ∃ i, u i ≠ 0) (hj : ∃ j, rationalCharacteristicPartial j t ≠ 0)
    (huk : u k = 0) (hbu : b ⬝ᵥ u = 0)
    (d : Fin 3 → K)
    (hd : (fun i => algebraMap K (E K) (d i)) ⬝ᵥ w = 0) :
    (fun i => algebraMap K (E K) (d i)) ᵥ* rationalCharacteristicJacobian V = 0 := by
  classical
  let g := algebraMap K (E K)
  let e : Fin 3 → E K := fun i => g (d i)
  obtain ⟨i, hi⟩ := hi
  obtain ⟨j, hj⟩ := hj
  have hdu : e ⬝ᵥ u = 0 := by
    have he := congrArg (rationalCharacteristicPartial (K := K) j) hd
    change rationalCharacteristicPartial j (∑ m : Fin 3, g (d m) * w m) =
      rationalCharacteristicPartial j 0 at he
    have hconst (m : Fin 3) : rationalCharacteristicPartial j (g (d m)) = 0 := by
      change rationalCharacteristicPartial j (algebraMap K (E K) (d m)) = 0
      exact Derivation.map_algebraMap _ _
    simp only [map_sum, map_zero, Derivation.leibniz, smul_eq_mul,
      hconst, mul_zero, add_zero, hfac] at he
    have he' : (∑ m : Fin 3, g (d m) * (s * u m * rationalCharacteristicPartial j t)) =
        (s * rationalCharacteristicPartial j t) * (e ⬝ᵥ u) := by
      rw [dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      change g (d m) * (s * u m * rationalCharacteristicPartial j t) =
        (s * rationalCharacteristicPartial j t) * (g (d m) * u m)
      ring
    rw [he'] at he
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hs hj)
  have hp := rankTwo_direction_normal_proportional w u b e k l i hk huk hi hl hn hbu hd hdu
  funext j
  change (∑ m : Fin 3, e m * rationalCharacteristicJacobian V m j) = 0
  have hsum : (∑ m : Fin 3, e m * rationalCharacteristicJacobian V m j) =
      e l * (∑ m : Fin 3, b m * rationalCharacteristicJacobian V m j) := by
    rw [Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro m _
    rw [hp m]
    ring
  have he := congrFun hb j
  change (∑ m : Fin 3, b m * rationalCharacteristicJacobian V m j) = 0 at he
  rw [hsum, he, mul_zero]

set_option maxHeartbeats 2000000 in
/-- Nonconstant direction: either the original Jacobian has a
nonzero ground-field left kernel, or the parameter supplied by
the rank-one machinery is a reduced quotient of affine polynomials. -/
theorem rankTwo_direction_affineParameter_or_constantNormal
    (V : I → E K) (w b : Fin 3 → E K) (k l : Fin 3)
    (hk : w k = 1) (hl : b l = 1)
    (hn : b ⬝ᵥ w = 0) (hb : b ᵥ* rationalCharacteristicJacobian V = 0)
    (hw : ∀ i, rankTwo_directionalDerivation w (w i) = 0)
    (hdw : ∀ j, (∑ i : Fin 3, b i * rationalCharacteristicPartial j (w i)) = 0)
    (hneq : rationalCharacteristicJacobian (rankTwo_directionLift w) ≠ 0) :
    (∃ d : Fin 3 → K, d ≠ 0 ∧
      (fun i => algebraMap K (E K) (d i)) ᵥ* rationalCharacteristicJacobian V = 0) ∨
    ∃ (t : E K) (p q : B K) (A Q : Fin 3 → P K),
      q ≠ 0 ∧ IsRelPrime p q ∧
      algebraMap (B K) (E K) p / algebraMap (B K) (E K) q = t ∧
      (p = MvPolynomial.C (p.coeff 0) +
        ∑ j : Fin 3, MvPolynomial.C ((pderiv j p).coeff 0) * X j) ∧
      (q = MvPolynomial.C (q.coeff 0) +
        ∑ j : Fin 3, MvPolynomial.C ((pderiv j q).coeff 0) * X j) ∧
      (∀ i, (Q i).eval₂ (algebraMap K (E K)) t ≠ 0) ∧
      (∀ i, w i = (A i).eval₂ (algebraMap K (E K)) t /
        (Q i).eval₂ (algebraMap K (E K)) t) ∧
      (∃ j, rationalCharacteristicPartial j t ≠ 0) ∧
      rankTwo_directionalDerivation w t = 0 := by
  classical
  obtain ⟨t, A, Q, U, s, hq, hrep, hs, hfac, hi, hj, huk, hbu, hdt⟩ :=
    rankTwo_direction_commonParameter w b k l hk hl hn hw hdw hneq
  obtain ⟨W, r, hr, hW⟩ := rankTwo_direction_polynomialVector w t A Q hq hrep
  let ev : P K →+* E K := _root_.Polynomial.eval₂RingHom (algebraMap K (E K)) t
  by_cases hind : ∀ d : Fin 3 → K,
      (∑ j : Fin 3, _root_.Polynomial.C (d j) * W j) = 0 → d = 0
  · right
    have hnc (c : K) : t ≠ algebraMap K (E K) c := by
      intro hc
      obtain ⟨j, hj⟩ := hj
      apply hj
      rw [hc, Derivation.map_algebraMap]
    obtain ⟨p, q, hqn, hcop, hpos, hrepr⟩ :=
      rationalParameter_exists_reduced_nonconstant t hnc
    have hlift := rankTwo_direction_trace_lift w t W r hr hW hdt p q hqn hcop hpos hrepr
    obtain ⟨hp, hqa⟩ := rankOne_affine_parameters_of_lifted_trace_independent p q W hlift hind
    exact ⟨t, p, q, A, Q, hqn, hcop, hrepr, hp, hqa, hq, hrep, hj, hdt⟩
  · left
    push_neg at hind
    obtain ⟨d, hd, hd0⟩ := hind
    have he := congrArg ev hd
    change ev (∑ j : Fin 3, _root_.Polynomial.C (d j) * W j) = ev 0 at he
    rw [map_sum, map_zero] at he
    have he' : (∑ j : Fin 3, ev (_root_.Polynomial.C (d j) * W j)) =
        r * ((fun j => algebraMap K (E K) (d j)) ⬝ᵥ w) := by
      rw [dotProduct, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro j _
      change (_root_.Polynomial.C (d j) * W j).eval₂ (algebraMap K (E K)) t =
        r * (algebraMap K (E K) (d j) * w j)
      rw [_root_.Polynomial.eval₂_mul, _root_.Polynomial.eval₂_C, hW]
      ring
    rw [he'] at he
    have hdw' := (mul_eq_zero.mp he).resolve_left hr
    exact ⟨d, hd0, rankTwo_direction_constantNormal_transfer V w b k l hk hl hn hb
      t (fun i => (U i).eval₂ (algebraMap K (E K)) t) s hs hfac hi hj huk hbu d hdw'⟩

end
end HC4.Polynomial.RankThreeCubic
