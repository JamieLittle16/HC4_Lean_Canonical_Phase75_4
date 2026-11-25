import HC4.Polynomial.RationalCharacteristicRankTwoAffineGradient

/-!
# Rank-one reduction for the normalized straight direction

The normal annihilates the derivative of the normalized straight
direction by the polynomial affine-gradient theorem. The coordinate
normal of its fixed component annihilates that derivative as well.
These two normals are independent because the actual direction
pairs to one with the coordinate normal and to zero with the
source normal.

Consequently the direction has rank at most one, even though the
original velocity has rank two. In the nonconstant case we can
reuse the verified rank-one common-parameter theorem, including
Lüroth, without a new rationality premise.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

section Algebra

variable {F : Type*} [Field F]

/-- A matrix annihilated by a normalized coordinate normal and by
a nonzero normal orthogonal to the original direction has all
two-by-two minors zero. -/
theorem rankTwo_direction_minors_zero
    (A : Matrix (Fin 3) (Fin 3) F) (w b : Fin 3 → F)
    (k l : Fin 3) (hk : w k = 1) (hl : b l = 1)
    (hn : b ⬝ᵥ w = 0) (hb : b ᵥ* A = 0)
    (hrow : ∀ j, A k j = 0) :
    ∀ a d i j : Fin 3, A a i * A d j = A a j * A d i := by
  classical
  let e : Fin 3 → F := fun i => if i = k then 1 else 0
  have he : e ᵥ* A = 0 := by
    funext j
    change (∑ i : Fin 3, (if i = k then 1 else 0) * A i j) = 0
    rw [Finset.sum_eq_single k]
    · simp [hrow]
    · intro i _ hi
      simp [hi]
    · simp
  intro a d i j
  by_contra hm
  have hr := rankTwo_rank_ge_two_of_minor A a d i j hm
  have hprop (i : Fin 3) : b i = e i * b k := by
    have h := rankTwo_leftKernel_minors_zero A hr e b he hb k i
    have hek : e k = 1 := by simp [e]
    rw [hek, one_mul] at h
    exact h
  have hbk : b k = 0 := by
    change (∑ i : Fin 3, b i * w i) = 0 at hn
    have hsum : (∑ i : Fin 3, b i * w i) = b k := by
      calc
        (∑ i : Fin 3, b i * w i) =
            ∑ i : Fin 3, e i * b k * w i := by
          apply Finset.sum_congr rfl
          intro i _
          rw [← hprop i]
        _ = b k := by
          change (∑ i : Fin 3, ((if i = k then 1 else 0) * b k) * w i) = b k
          rw [Finset.sum_eq_single k]
          · simp [hk]
          · intro i _ hi
            simp [hi]
          · simp
    rw [hsum] at hn
    exact hn
  have hz := hprop l
  rw [hl, hbk, mul_zero] at hz
  exact one_ne_zero hz

/-- A nonzero outer product has a nonzero column scalar and a
nonzero entry in its image factor. -/
theorem rankTwo_nonzero_outer_factor
    (A : Matrix (Fin 3) (Fin 3) F) (u d : Fin 3 → F) (s : F)
    (hn : A ≠ 0) (h : ∀ i j, A i j = s * u i * d j) :
    ∃ i j : Fin 3, u i ≠ 0 ∧ d j ≠ 0 := by
  classical
  have he : ∃ i j : Fin 3, A i j ≠ 0 := by
    by_contra hz
    apply hn
    apply Matrix.ext
    intro i j
    by_contra hij
    exact hz ⟨i, j, hij⟩
  obtain ⟨i, j, hij⟩ := he
  refine ⟨i, j, ?_, ?_⟩
  · intro hz
    exact hij (by rw [h, hz, mul_zero, zero_mul])
  · intro hz
    exact hij (by rw [h, hz, mul_zero])

end Algebra

variable {K : Type*} [Field K] [CharZero K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev I := Unit ⊕ Fin 3
private abbrev S (K : Type*) [Field K] := MvPolynomial I K
private abbrev P (K : Type*) [Field K] := _root_.Polynomial K

/-- Package the straight direction in the existing characteristic
Jacobian API. The longitudinal component is only a dummy constant,
not an assertion that this direction is a source characteristic. -/
def rankTwo_directionLift (w : Fin 3 → E K) : I → E K :=
  Sum.elim (fun _ => 1) w

/-- The source normal forces rank at most one for the derivative
of the straight direction. -/
theorem rankTwo_directionJacobian_minors
    (w b : Fin 3 → E K) (k l : Fin 3)
    (hk : w k = 1) (hl : b l = 1) (hn : b ⬝ᵥ w = 0)
    (hb : ∀ j, (∑ i : Fin 3, b i * rationalCharacteristicPartial j (w i)) = 0) :
    ∀ a d i j : Fin 3,
      rationalCharacteristicJacobian (rankTwo_directionLift w) a i *
        rationalCharacteristicJacobian (rankTwo_directionLift w) d j =
      rationalCharacteristicJacobian (rankTwo_directionLift w) a j *
        rationalCharacteristicJacobian (rankTwo_directionLift w) d i := by
  let A := rationalCharacteristicJacobian (rankTwo_directionLift w)
  have hnormal : b ᵥ* A = 0 := by
    funext j
    exact hb j
  have hrow (j : Fin 3) : A k j = 0 := by
    change rationalCharacteristicPartial j (w k) = 0
    rw [hk, Derivation.map_one_eq_zero]
  exact rankTwo_direction_minors_zero A w b k l hk hl hn hnormal hrow

/-- In the nonconstant case the common parameter also carries a
nonzero derivative vector annihilated by the source normal, with
zero normalized-coordinate component. The parameter is itself
invariant along the straight direction.

This is purely the common-parameter theorem and its derivative
factorization, not an application of the rank-one Hessian
obstruction to a matrix which may not be self-adjoint. -/
theorem rankTwo_direction_commonParameter
    (w b : Fin 3 → E K) (k l : Fin 3)
    (hk : w k = 1) (hl : b l = 1) (hn : b ⬝ᵥ w = 0)
    (hw : ∀ i, rankTwo_directionalDerivation w (w i) = 0)
    (hb : ∀ j, (∑ i : Fin 3, b i * rationalCharacteristicPartial j (w i)) = 0)
    (hneq : rationalCharacteristicJacobian (rankTwo_directionLift w) ≠ 0) :
    ∃ (t : E K) (A Q U : Fin 3 → P K) (s : E K),
      (∀ i, (Q i).eval₂ (algebraMap K (E K)) t ≠ 0) ∧
      (∀ i, w i = (A i).eval₂ (algebraMap K (E K)) t /
        (Q i).eval₂ (algebraMap K (E K)) t) ∧
      s ≠ 0 ∧
      (∀ i j, rationalCharacteristicPartial j (w i) =
        s * (U i).eval₂ (algebraMap K (E K)) t * rationalCharacteristicPartial j t) ∧
      (∃ i : Fin 3, (U i).eval₂ (algebraMap K (E K)) t ≠ 0) ∧
      (∃ j : Fin 3, rationalCharacteristicPartial j t ≠ 0) ∧
      (U k).eval₂ (algebraMap K (E K)) t = 0 ∧
      (∑ i : Fin 3, b i * (U i).eval₂ (algebraMap K (E K)) t) = 0 ∧
      rankTwo_directionalDerivation w t = 0 := by
  classical
  let W := rankTwo_directionLift w
  let N := rationalCharacteristicJacobian W
  obtain ⟨t, A, Q, hq, hrep⟩ := rankOne_commonParameter W hneq
    (fun a b' i j => rankTwo_directionJacobian_minors w b k l hk hl hn hb a i b' j)
  obtain ⟨U, s, hs, hfactor⟩ :=
    rationalCharacteristic_commonParameter_factor W t A Q hq hrep
  let u : Fin 3 → E K := fun i => (U i).eval₂ (algebraMap K (E K)) t
  let d : Fin 3 → E K := fun j => rationalCharacteristicPartial j t
  have hfac (i j : Fin 3) : rationalCharacteristicPartial j (w i) =
      s * u i * d j := hfactor i j
  obtain ⟨i, j, hi, hj⟩ := rankTwo_nonzero_outer_factor N u d s hneq hfactor
  have huk : u k = 0 := by
    have he := hfac k j
    rw [hk, Derivation.map_one_eq_zero] at he
    exact (mul_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right hj)).resolve_left hs
  have hbu : (∑ i : Fin 3, b i * u i) = 0 := by
    have he := hb j
    simp only [hfac] at he
    have he' : (∑ i : Fin 3, b i * (s * u i * d j)) =
        (s * d j) * (∑ i : Fin 3, b i * u i) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    rw [he'] at he
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hs hj)
  have hdt : rankTwo_directionalDerivation w t = 0 := by
    have he := hw i
    rw [rankTwo_directionalDerivation_apply] at he
    simp only [hfac] at he
    have he' : (∑ j : Fin 3, w j * (s * u i * d j)) =
        (s * u i) * (∑ j : Fin 3, w j * d j) := by
      rw [Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro m _
      ring
    rw [he'] at he
    rw [rankTwo_directionalDerivation_apply]
    exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hs hi)
  exact ⟨t, A, Q, U, s, hq, hrep, hs, hfac, ⟨i, hi⟩, ⟨j, hj⟩, huk, hbu, hdt⟩

/-- A constant direction is genuinely ground-field-valued, not
merely invariant along its own fibre. -/
theorem rankTwo_direction_constant
    (w : Fin 3 → E K)
    (h : rationalCharacteristicJacobian (rankTwo_directionLift w) = 0) :
    ∃ c : Fin 3 → K, ∀ i, w i = algebraMap K (E K) (c i) :=
  rationalCharacteristic_constant_of_jacobian_zero (rankTwo_directionLift w) h

set_option maxHeartbeats 2000000 in
/-- Source-level reduction: the normalized direction is either
ground-field constant or rationally parametrized by one parameter.
Retain the normal, original rank-two kernel, and derivative
annihilation rather than replacing the actual source by an
unrelated rank-one characteristic. -/
theorem rankTwo_source_directionParameter
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
      b ᵥ* rationalCharacteristicJacobian V = 0 ∧ b ⬝ᵥ w = 0 ∧
      (∀ i, rankTwo_directionalDerivation w (w i) = 0) ∧
      (∀ i, rankTwo_directionalDerivation w (b i) = 0) ∧
      (∀ i, rankTwo_fibreEval w (pderiv i (referenceSlice a L)) =
        _root_.Polynomial.C (algebraMap (B K) (E K) (pderiv i (referenceSlice a L))) +
          _root_.Polynomial.X * _root_.Polynomial.C (c * b i)) ∧
      (∀ j, (∑ i : Fin 3, b i * rationalCharacteristicPartial j (w i)) = 0) ∧
      ((∃ d : Fin 3 → K, ∀ i, w i = algebraMap K (E K) (d i)) ∨
        ∃ (t : E K) (A Q U : Fin 3 → P K) (s : E K),
          (∀ i, (Q i).eval₂ (algebraMap K (E K)) t ≠ 0) ∧
          (∀ i, w i = (A i).eval₂ (algebraMap K (E K)) t /
            (Q i).eval₂ (algebraMap K (E K)) t) ∧
          s ≠ 0 ∧
          (∀ i j, rationalCharacteristicPartial j (w i) =
            s * (U i).eval₂ (algebraMap K (E K)) t * rationalCharacteristicPartial j t) ∧
          (∃ i : Fin 3, (U i).eval₂ (algebraMap K (E K)) t ≠ 0) ∧
          (∃ j : Fin 3, rationalCharacteristicPartial j t ≠ 0) ∧
          (U k).eval₂ (algebraMap K (E K)) t = 0 ∧
          (∑ i : Fin 3, b i * (U i).eval₂ (algebraMap K (E K)) t) = 0 ∧
          rankTwo_directionalDerivation w t = 0) := by
  classical
  obtain ⟨w, b, k, l, c, hk, hl, hc, hw, hb, hn, hww, hbb, hg, hdw⟩ :=
    rankTwo_source_affineGradient a L V hV hreg hgrad hm
  refine ⟨w, b, k, l, c, hk, hl, hc, hw, hb, hn, hww, hbb, hg, hdw, ?_⟩
  by_cases hz : rationalCharacteristicJacobian (rankTwo_directionLift w) = 0
  · exact Or.inl (rankTwo_direction_constant w hz)
  · exact Or.inr (rankTwo_direction_commonParameter w b k l hk hl hn hww hdw hz)

end
end HC4.Polynomial.RankThreeCubic
