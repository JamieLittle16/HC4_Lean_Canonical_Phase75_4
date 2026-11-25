import HC4.Polynomial.RationalCharacteristicRankTwoNormalParameter

/-!
# Closure of the nonconstant straight-direction branch

For an affine quotient parameter, dt is proportional to a - t d
with a,d constant. If both the direction and its tangent annihilate
dt, differentiating (a - t d) · w = 0 forces d · w = 0 and then
a · w = 0. The parameter is nonconstant so one of a,d is nonzero.

The preceding normal-derivative dichotomy handles the other case.
Thus a nonconstant normalized fibre direction always supplies the
original constant left-kernel relation.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev I := Unit ⊕ Fin 3
private abbrev S (K : Type*) [Field K] := MvPolynomial I K
private abbrev P (K : Type*) [Field K] := _root_.Polynomial K

/-- A nonconstant affine quotient whose differential kills both
the direction and its derivative factor gives a constant
orthogonal covector of the direction. -/
theorem rankTwo_affineParameter_constantDirectionNormal
    (w u : Fin 3 → E K) (t s : E K)
    (p q : B K) (hq : q ≠ 0)
    (hrep : algebraMap (B K) (E K) p / algebraMap (B K) (E K) q = t)
    (hp : p = MvPolynomial.C (p.coeff 0) +
      ∑ j : Fin 3, MvPolynomial.C ((pderiv j p).coeff 0) * X j)
    (hqa : q = MvPolynomial.C (q.coeff 0) +
      ∑ j : Fin 3, MvPolynomial.C ((pderiv j q).coeff 0) * X j)
    (hfac : ∀ i j, rationalCharacteristicPartial j (w i) =
      s * u i * rationalCharacteristicPartial j t)
    (hj : ∃ j, rationalCharacteristicPartial j t ≠ 0)
    (hw : rankTwo_directionalDerivation w t = 0)
    (hu : rankTwo_directionalDerivation u t = 0) :
    ∃ d : Fin 3 → K, d ≠ 0 ∧
      (fun i => algebraMap K (E K) (d i)) ⬝ᵥ w = 0 := by
  classical
  let a : Fin 3 → K := fun i => (pderiv i p).coeff 0
  let d : Fin 3 → K := fun i => (pderiv i q).coeff 0
  let g := algebraMap (B K) (E K)
  let e := algebraMap K (E K)
  let A : Fin 3 → E K := fun i => e (a i)
  let D : Fin 3 → E K := fun i => e (d i)
  have hC (z : K) : g (MvPolynomial.C z) = e z :=
    (IsScalarTower.toAlgHom K (B K) (E K)).commutes z
  have hdiff (j : Fin 3) : rationalCharacteristicPartial j t * g q =
      A j - t * D j := by
    have h := rationalParameter_cleared_partial p q hq j
    change rationalCharacteristicPartial j (g p / g q) * g q =
      g (pderiv j p) - (g p / g q) * g (pderiv j q) at h
    rw [hrep, rankOne_affine_partial_eq_C p hp j,
      rankOne_affine_partial_eq_C q hqa j, hC, hC] at h
    exact h
  have horth (v : Fin 3 → E K) (hv : rankTwo_directionalDerivation v t = 0) :
      A ⬝ᵥ v - t * (D ⬝ᵥ v) = 0 := by
    change (∑ i : Fin 3, A i * v i) - t * (∑ i : Fin 3, D i * v i) = 0
    rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
    have he : (∑ i : Fin 3, (A i * v i - t * (D i * v i))) =
        g q * rankTwo_directionalDerivation v t := by
      rw [rankTwo_directionalDerivation_apply, Finset.mul_sum]
      apply Finset.sum_congr rfl
      intro i _
      calc
        _ = (A i - t * D i) * v i := by ring
        _ = _ := by rw [← hdiff i]; ring
    rw [he, hv, mul_zero]
  have hAw := sub_eq_zero.mp (horth w hw)
  have hAu := sub_eq_zero.mp (horth u hu)
  obtain ⟨j, hj⟩ := hj
  let δ := rationalCharacteristicPartial (K := K) j
  have hDA (i : Fin 3) : δ (A i) = 0 := Derivation.map_algebraMap δ (a i)
  have hDD (i : Fin 3) : δ (D i) = 0 := Derivation.map_algebraMap δ (d i)
  have hlin (v : Fin 3 → E K) (hv : ∀ i, δ (v i) = s * u i * δ t)
      (C : Fin 3 → E K) (hC : ∀ i, δ (C i) = 0) :
      δ (C ⬝ᵥ v) = (s * δ t) * (C ⬝ᵥ u) := by
    rw [rankTwo_derivation_dot]
    change (∑ i : Fin 3, C i * δ (v i)) +
      (∑ i : Fin 3, δ (C i) * v i) = _
    simp only [hC, zero_mul, Finset.sum_const_zero, add_zero, hv]
    rw [dotProduct, Finset.mul_sum]
    apply Finset.sum_congr rfl
    intro i _
    ring
  have he := congrArg δ hAw
  change δ (A ⬝ᵥ w) = δ (t * (D ⬝ᵥ w)) at he
  rw [Derivation.leibniz, smul_eq_mul, smul_eq_mul,
    hlin w (fun i => hfac i j) A hDA,
    hlin w (fun i => hfac i j) D hDD, hAu] at he
  have hz : δ t * (D ⬝ᵥ w) = 0 := by linear_combination -he
  have hDw := (mul_eq_zero.mp hz).resolve_left hj
  have hAw0 : A ⬝ᵥ w = 0 := by rw [hAw, hDw, mul_zero]
  by_cases hd : d = 0
  · have ha : a ≠ 0 := by
      intro ha
      have hAz : A j = 0 := by simp [A, ha]
      have hDz : D j = 0 := by simp [D, hd]
      have he := hdiff j
      rw [hAz, hDz, mul_zero, sub_zero] at he
      have hqg : g q ≠ 0 := by
        simpa only [map_zero] using (IsFractionRing.injective (B K) (E K)).ne hq
      exact (mul_ne_zero hj hqg) he
    exact ⟨a, ha, hAw0⟩
  · exact ⟨d, hd, hDw⟩

set_option maxHeartbeats 3000000 in
/-- The nonconstant normalized straight direction is fully rigid.
All hypotheses on the parameter are produced from the direction
itself by the verified common-parameter and trace-lift theorems. -/
theorem rankTwo_nonconstantDirection_leftKernel
    (V : I → E K) (w b : Fin 3 → E K) (k l : Fin 3)
    (hr : 2 ≤ (rationalCharacteristicJacobian V).rank)
    (h3 : rationalCharacteristicJacobian V ^ 3 = 0)
    (hk : w k = 1) (hl : b l = 1)
    (hwN : rationalCharacteristicJacobian V *ᵥ w = 0)
    (hn : b ⬝ᵥ w = 0) (hb : b ᵥ* rationalCharacteristicJacobian V = 0)
    (hw : ∀ i, rankTwo_directionalDerivation w (w i) = 0)
    (hdw : ∀ j, (∑ i : Fin 3, b i * rationalCharacteristicPartial j (w i)) = 0)
    (hneq : rationalCharacteristicJacobian (rankTwo_directionLift w) ≠ 0) :
    ∃ d : Fin 3 → K, d ≠ 0 ∧
      (fun i => algebraMap K (E K) (d i)) ᵥ* rationalCharacteristicJacobian V = 0 := by
  classical
  rcases rankTwo_direction_affineParameter_or_constantNormal V w b k l hk hl hn hb hw hdw hneq
    with h | h
  · exact h
  · obtain ⟨t, p, q, A, Q, hq, _, hrepr, hp, hqa, hQ, hrep, hj, hdt⟩ := h
    obtain ⟨U, s, hs, hfactor⟩ :=
      rationalCharacteristic_commonParameter_factor (rankTwo_directionLift w) t A Q hQ hrep
    let u : Fin 3 → E K := fun i => (U i).eval₂ (algebraMap K (E K)) t
    let N := rationalCharacteristicJacobian (rankTwo_directionLift w)
    have hfac (i j : Fin 3) : rationalCharacteristicPartial j (w i) =
        s * u i * rationalCharacteristicPartial j t := hfactor i j
    obtain ⟨i, j, hi, hj'⟩ := rankTwo_nonzero_outer_factor N u
      (fun j => rationalCharacteristicPartial j t) s hneq hfactor
    have huk : u k = 0 := by
      have he := hfac k j
      rw [hk, Derivation.map_one_eq_zero] at he
      exact (mul_eq_zero.mp ((mul_eq_zero.mp he.symm).resolve_right hj')).resolve_left hs
    have hbu : (∑ i : Fin 3, b i * u i) = 0 := by
      have he := hdw j
      simp only [hfac] at he
      have he' : (∑ i : Fin 3, b i * (s * u i * rationalCharacteristicPartial j t)) =
          (s * rationalCharacteristicPartial j t) * (∑ i : Fin 3, b i * u i) := by
        rw [Finset.mul_sum]
        apply Finset.sum_congr rfl
        intro m _
        ring
      rw [he'] at he
      exact (mul_eq_zero.mp he).resolve_left (mul_ne_zero hs hj')
    rcases rankTwo_parameter_tangent_or_constantNormal V w b k l hr h3 hk hl hwN hn hb
      t A Q U s hQ hrep hfac ⟨i, hi⟩ hj huk hbu with ht | hc
    · obtain ⟨d, hd0, hd⟩ := rankTwo_affineParameter_constantDirectionNormal
        w u t s p q hq hrepr hp hqa hfac hj hdt ht
      exact ⟨d, hd0, rankTwo_direction_constantNormal_transfer V w b k l hk hl hn hb
        t u s hs hfac ⟨i, hi⟩ hj huk hbu d hd⟩
    · exact hc

set_option maxHeartbeats 2000000 in
/-- Source-level endpoint: either the original adjugate has its
constant annihilator, or the source has a genuinely constant
nonzero straight direction with the earlier affine-gradient
transport identities. -/
theorem rankTwo_source_constantDirection_or_adjugate
    (a : K) (L : S K) (V : I → E K)
    (hdet : (hessian L).det = 0)
    (hV : V (.inl ()) = 1)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L)))
    (hm : ¬ ∀ a b i j : Fin 3,
      rationalCharacteristicJacobian V a b * rationalCharacteristicJacobian V i j =
        rationalCharacteristicJacobian V a j * rationalCharacteristicJacobian V i b) :
    (∃ d : I → K, d ≠ 0 ∧
      (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0) ∨
    ∃ (d : Fin 3 → K) (b : Fin 3 → E K) (k l : Fin 3) (c : E K),
      d k = 1 ∧ b l = 1 ∧ c ≠ 0 ∧
      rationalCharacteristicJacobian V *ᵥ (fun i => algebraMap K (E K) (d i)) = 0 ∧
      b ᵥ* rationalCharacteristicJacobian V = 0 ∧
      b ⬝ᵥ (fun i => algebraMap K (E K) (d i)) = 0 ∧
      (∀ i, rankTwo_fibreEval (fun j => algebraMap K (E K) (d j))
        (pderiv i (referenceSlice a L)) =
        _root_.Polynomial.C (algebraMap (B K) (E K) (pderiv i (referenceSlice a L))) +
          _root_.Polynomial.X * _root_.Polynomial.C (c * b i)) := by
  classical
  obtain ⟨w, b, k, l, c, hk, hl, hc, hw, hb, hn, hww, _, hg, hdw⟩ :=
    rankTwo_source_affineGradient a L V hV hreg hgrad hm
  by_cases hz : rationalCharacteristicJacobian (rankTwo_directionLift w) = 0
  · right
    obtain ⟨d, hd⟩ := rankTwo_direction_constant w hz
    have he : w = fun i => algebraMap K (E K) (d i) := funext hd
    have hdk : d k = 1 := by
      apply (algebraMap K (E K)).injective
      rw [← hd k, hk, map_one]
    rw [he] at hw hn hg
    exact ⟨d, b, k, l, c, hdk, hl, hc, hw, hb, hn, hg⟩
  · left
    have hr : 2 ≤ (rationalCharacteristicJacobian V).rank := by
      by_contra h
      apply hm
      intro a b i j
      by_contra hz
      exact h (rankTwo_rank_ge_two_of_minor _ a i b j hz)
    have h3 := rationalCharacteristicJacobian_cube_eq_zero a L V hV hreg
      (fun i => hgrad (.inr i))
    obtain ⟨d, hd0, hd⟩ :=
      rankTwo_nonconstantDirection_leftKernel V w b k l hr h3 hk hl hw hn hb hww hdw hz
    obtain ⟨e, he0, he⟩ := rationalCharacteristic_exists_annihilator_of_constant_leftKernel
      V hV d hd0 hd
    exact ⟨e, he0, rationalCharacteristic_adjugate_annihilator a L V e hdet hV hreg hgrad he⟩

end
end HC4.Polynomial.RankThreeCubic
