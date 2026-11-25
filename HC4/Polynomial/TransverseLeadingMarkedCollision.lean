import HC4.Polynomial.TransverseLeadingFixedPower
import HC4.Polynomial.RankThreeCubicDetOneWeightFivePoleSlice
import HC4.Polynomial.RankThreeCubicDetOneRankThreeKernelTraceIsotropy
import HC4.Polynomial.RankThreeCubicDetOnePrincipalCofactorKernelLine
import HC4.Polynomial.RankThreeCubicPoleJacobiBridge
import HC4.Valuation.ParameterFirstLayerBridge
import HC4.Valuation.ParameterGapSecondJet
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelMarkedAxisFirstContactFace
import Mathlib.Tactic
import HC4.Polynomial.TransverseLeadingSchurFoundation
import HC4.Polynomial.TransverseLeadingStationary
import HC4.Polynomial.TransverseLeadingNilpotent
import HC4.Polynomial.TransverseLeadingCorrectionDegree

/-!
# Marked-axis collision and mixed-gap rigidity

Actual marked gradient curves, low-grade extraction, pre-gap propagation,
late-gap collision exclusion, and first mixed-gap endpoint divisibility.
The subsequent prime-factor and mixed-pole arguments consume these results.
-/

namespace HC4.Polynomial.RankThreeCubic

open HC4.Newton HC4.Valuation
open scoped BigOperators Matrix

noncomputable section

variable {R : Type*} [CommRing R]
variable {K : Type*} [Field K] [CharZero K]

open MvPolynomial

private abbrev StationarySource (K : Type*) [Field K] :=
  MvPolynomial (Unit ⊕ Fin 3) K

private abbrev StationaryExponent := (Unit ⊕ Fin 3) →₀ ℕ

private abbrev LineTime (K : Type*) [Field K] :=
  _root_.Polynomial (MvPolynomial (Fin 3) K)

/-! ## A collision obstruction directly on the marked gradient curve

The original Hessian determinant implies a Bezout identity for the
derivative of the actual marked-axis gradient, not just pointwise
nonvanishing over the ground field. Consequently a collision cannot
be carried by a rank-one polynomial gradient curve, even when the
longitudinal degree is large.
-/

def stationaryAxisTrace : StationarySource K →ₐ[K] _root_.Polynomial K :=
  lineEval (fun _ => 0) (Sum.elim (fun _ : Unit => 1) (fun _ : Fin 3 => 0))

theorem stationaryAxisTrace_eval (P : StationarySource K) (t : K) :
    (stationaryAxisTrace P).eval t = stationaryAxisEval t P := by
  induction P using MvPolynomial.induction_on with
  | C c => simp [stationaryAxisTrace, stationaryAxisEval, lineEval]
  | add p q hp hq =>
    simp only [map_add, _root_.Polynomial.eval_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, _root_.Polynomial.eval_mul, map_mul, hp]
    cases i with
    | inl u => cases u; simp [stationaryAxisTrace, stationaryAxisEval, lineEval]
    | inr j => simp [stationaryAxisTrace, stationaryAxisEval, lineEval]

theorem stationaryAxisTrace_derivative (P : StationarySource K) :
    (stationaryAxisTrace P).derivative = stationaryAxisTrace (pderiv (.inl ()) P) := by
  classical
  change (lineEval (fun _ => (0 : K))
    (Sum.elim (fun _ : Unit => 1) (fun _ : Fin 3 => 0)) P).derivative = _
  rw [transverse_lineEval_derivative, Fintype.sum_sum_type]
  simp [stationaryAxisTrace]

/-- The cofactor row is an explicit polynomial Bezout certificate
for the tangent vector of the actual marked gradient curve. -/
theorem stationaryAxisTrace_gradient_bezout
    (F : StationarySource K) {δ : K}
    (hdet : hessianDeterminant F = MvPolynomial.C δ) :
    let A := (stationaryAxisTrace (K := K)).toRingHom.mapMatrix (hessian F)
    ∑ i : Unit ⊕ Fin 3,
      (stationaryAxisTrace (pderiv i F)).derivative * A.adjugate (.inl ()) i =
        _root_.Polynomial.C δ := by
  classical
  let A := (stationaryAxisTrace (K := K)).toRingHom.mapMatrix (hessian F)
  have hA : A.det = _root_.Polynomial.C δ := by
    change ((stationaryAxisTrace (K := K)).toRingHom.mapMatrix (hessian F)).det = _
    rw [← RingHom.map_det]
    change stationaryAxisTrace (hessianDeterminant F) = _
    rw [hdet]
    simp [stationaryAxisTrace, lineEval]
  change (∑ i : Unit ⊕ Fin 3,
    (stationaryAxisTrace (pderiv i F)).derivative * A.adjugate (.inl ()) i) = _
  calc
    _ = ∑ i : Unit ⊕ Fin 3, A i (.inl ()) * A.adjugate (.inl ()) i := by
      apply Finset.sum_congr rfl
      intro i _
      rw [stationaryAxisTrace_derivative]
      rfl
    _ = A.det := (Matrix.det_eq_sum_mul_adjugate_col A (.inl ())).symm
    _ = _ := hA

/-- No nonconstant polynomial can divide every component of the
marked gradient tangent. This holds without a regular transverse
anchor and without any degree cap on the source. -/
theorem stationaryAxisTrace_commonDerivativeDivisor_degree_zero
    (F : StationarySource K) {δ : K} (hδ : δ ≠ 0)
    (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (D : _root_.Polynomial K)
    (hD : ∀ i : Unit ⊕ Fin 3, D ∣ (stationaryAxisTrace (pderiv i F)).derivative) :
    D.natDegree = 0 := by
  classical
  let A := (stationaryAxisTrace (K := K)).toRingHom.mapMatrix (hessian F)
  choose Q hQ using hD
  have h := stationaryAxisTrace_gradient_bezout F hdet
  change (∑ i : Unit ⊕ Fin 3, (stationaryAxisTrace (pderiv i F)).derivative *
    A.adjugate (.inl ()) i) = _ at h
  let E := ∑ i : Unit ⊕ Fin 3, Q i * A.adjugate (.inl ()) i
  have he : D * E = _root_.Polynomial.C δ := by
    dsimp [E]
    rw [Finset.mul_sum]
    calc
      _ = ∑ i : Unit ⊕ Fin 3, (stationaryAxisTrace (pderiv i F)).derivative *
          A.adjugate (.inl ()) i := by
        apply Finset.sum_congr rfl
        intro i _
        rw [hQ i, mul_assoc]
      _ = _ := h
  have hne : D * E ≠ 0 := by rw [he]; exact _root_.Polynomial.C_ne_zero.mpr hδ
  have hd : D ≠ 0 := by
    intro hz
    apply hne
    rw [hz, zero_mul]
  have he' : E ≠ 0 := by
    intro hz
    apply hne
    rw [hz, mul_zero]
  have hdegree := congrArg _root_.Polynomial.natDegree he
  rw [_root_.Polynomial.natDegree_mul' (mul_ne_zero
    (_root_.Polynomial.leadingCoeff_ne_zero.mpr hd)
    (_root_.Polynomial.leadingCoeff_ne_zero.mpr he')),
    _root_.Polynomial.natDegree_C] at hdegree
  omega

private theorem sourceTime_derivative_constant_of_equal_endpoints
    (P : _root_.Polynomial K) (c : K)
    (h : P.derivative = _root_.Polynomial.C c)
    (he : P.eval 1 = P.eval 0) : P.derivative = 0 := by
  let Q := P - _root_.Polynomial.C c * _root_.Polynomial.X
  have hQ : Q.derivative = 0 := by
    change (P - _root_.Polynomial.C c * _root_.Polynomial.X).derivative = 0
    rw [map_sub, h, _root_.Polynomial.derivative_mul,
      _root_.Polynomial.derivative_C, _root_.Polynomial.derivative_X]
    simp
  have hc := _root_.Polynomial.eq_C_of_derivative_eq_zero hQ
  have h1 := congrArg (fun q : _root_.Polynomial K => q.eval 1) hc
  have h0 := congrArg (fun q : _root_.Polynomial K => q.eval 0) hc
  change (P - _root_.Polynomial.C c * _root_.Polynomial.X).eval 1 =
    (_root_.Polynomial.C (Q.coeff 0)).eval 1 at h1
  change (P - _root_.Polynomial.C c * _root_.Polynomial.X).eval 0 =
    (_root_.Polynomial.C (Q.coeff 0)).eval 0 at h0
  simp only [_root_.Polynomial.eval_sub, _root_.Polynomial.eval_mul,
    _root_.Polynomial.eval_C, _root_.Polynomial.eval_X, mul_one, mul_zero, sub_zero] at h1 h0
  have hz : c = 0 := by
    rw [he, h0] at h1
    linear_combination -h1
  rw [h, hz, map_zero]

/-- A marked collision cannot have its entire gradient trace in an
affine line, even if the source and the trace have arbitrary degree.
The tangent rank-one assumption is stated as an exact polynomial
identity, not a condition on only one evaluation point. -/
theorem stationaryAxisTrace_rankOne_markedCollision_impossible
    (F : StationarySource K) {δ : K} (hδ : δ ≠ 0)
    (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (hcoll : ∀ i : Unit ⊕ Fin 3,
      stationaryAxisEval 1 (pderiv i F) = stationaryAxisEval 0 (pderiv i F))
    (D : _root_.Polynomial K) (v : Unit ⊕ Fin 3 → K)
    (hline : ∀ i, (stationaryAxisTrace (pderiv i F)).derivative =
      _root_.Polynomial.C (v i) * D) : False := by
  classical
  have hD : ∀ i : Unit ⊕ Fin 3, D ∣ (stationaryAxisTrace (pderiv i F)).derivative := by
    intro i
    refine ⟨_root_.Polynomial.C (v i), ?_⟩
    rw [hline i, mul_comm]
  have hd := stationaryAxisTrace_commonDerivativeDivisor_degree_zero F hδ hdet D hD
  have hC := _root_.Polynomial.eq_C_of_natDegree_eq_zero hd
  have hz (i : Unit ⊕ Fin 3) : (stationaryAxisTrace (pderiv i F)).derivative = 0 := by
    apply sourceTime_derivative_constant_of_equal_endpoints _ (v i * D.coeff 0)
    · calc
        _ = _root_.Polynomial.C (v i) * D := hline i
        _ = _root_.Polynomial.C (v i) * _root_.Polynomial.C (D.coeff 0) :=
          congrArg (fun p => _root_.Polynomial.C (v i) * p) hC
        _ = _ := (_root_.Polynomial.C.map_mul _ _).symm
    · rw [stationaryAxisTrace_eval, stationaryAxisTrace_eval]
      exact hcoll i
  have hb := stationaryAxisTrace_gradient_bezout F hdet
  change (∑ i : Unit ⊕ Fin 3, (stationaryAxisTrace (pderiv i F)).derivative *
    ((stationaryAxisTrace (K := K)).toRingHom.mapMatrix (hessian F)).adjugate (.inl ()) i) = _ at hb
  simp only [hz, zero_mul, Finset.sum_const_zero] at hb
  exact hδ (_root_.Polynomial.C_eq_zero.mp hb.symm)




/-! ## Exact low-grade extraction on the marked axis

The entire marked gradient and its Hessian witness are determined
by the first three transverse grades of the ORIGINAL source.
No replacement potential is asserted to have constant determinant
away from that axis.
-/

/-- Only transverse grade zero survives the marked-axis substitution. -/
theorem stationaryAxisTrace_initialForm_zero (P : StationarySource K) :
    stationaryAxisTrace (initialForm transverseCubicWeight 0 P) =
      stationaryAxisTrace P := by
  classical
  have hz : stationaryAxisTrace (P - initialForm transverseCubicWeight 0 P) = 0 := by
    change MvPolynomial.aeval
      (fun i : Unit ⊕ Fin 3 =>
        _root_.Polynomial.C (0 : K) +
          _root_.Polynomial.C (Sum.elim (fun _ : Unit => 1) (fun _ : Fin 3 => 0) i) *
            _root_.Polynomial.X) (P - initialForm transverseCubicWeight 0 P) = 0
    apply MvPolynomial.aeval_eq_zero
    intro d hd
    have hw : Finsupp.weight transverseCubicWeight d ≠ 0 := by
      intro h
      apply hd
      simp [MvPolynomial.coeff_sub, coeff_initialForm, h]
    have he : ∃ j : Fin 3, d (.inr j) ≠ 0 := by
      by_contra! hn
      apply hw
      rw [transverseCubicWeight_eq_transverseSum]
      simp [hn]
    obtain ⟨j, hj⟩ := he
    exact ⟨.inr j, Finsupp.mem_support_iff.mpr hj, by simp⟩
  rw [map_sub, sub_eq_zero] at hz
  exact hz.symm

/-- The actual marked gradient component comes from exactly one
transverse source layer: zero for the longitudinal component and
one for each transverse component. -/
theorem stationaryAxisTrace_gradient_layer
    (F : StationarySource K) (i : Unit ⊕ Fin 3) :
    stationaryAxisTrace (pderiv i F) =
      stationaryAxisTrace (pderiv i (initialForm transverseCubicWeight
        (transverseCubicWeight i) F)) := by
  rw [pderiv_initialForm, sub_self, stationaryAxisTrace_initialForm_zero]

/-- Each entry of the actual marked Hessian comes from precisely the
source layer indexed by the sum of the two derivative weights. -/
theorem stationaryAxisTrace_hessian_layer
    (F : StationarySource K) (i j : Unit ⊕ Fin 3) :
    stationaryAxisTrace (hessian F i j) =
      stationaryAxisTrace (hessian (initialForm transverseCubicWeight
        (transverseCubicWeight i + transverseCubicWeight j) F) i j) := by
  rw [hessian_initialForm_entry,
    show transverseCubicWeight i + transverseCubicWeight j -
      transverseCubicWeight i - transverseCubicWeight j = 0 by ring,
    stationaryAxisTrace_initialForm_zero]

/-- The marked-axis Hessian determinant is an exact low-layer
certificate, independent of the remaining high source layers. -/
theorem stationaryAxisTrace_lowLayers_det
    (F : StationarySource K) {δ : K}
    (hdet : hessianDeterminant F = MvPolynomial.C δ) :
    (Matrix.of fun i j : Unit ⊕ Fin 3 =>
      stationaryAxisTrace (hessian (initialForm transverseCubicWeight
        (transverseCubicWeight i + transverseCubicWeight j) F) i j)).det =
      _root_.Polynomial.C δ := by
  classical
  let A := (stationaryAxisTrace (K := K)).toRingHom.mapMatrix (hessian F)
  have he : (Matrix.of fun i j : Unit ⊕ Fin 3 =>
      stationaryAxisTrace (hessian (initialForm transverseCubicWeight
        (transverseCubicWeight i + transverseCubicWeight j) F) i j)) = A := by
    apply Matrix.ext
    intro i j
    change stationaryAxisTrace (hessian (initialForm transverseCubicWeight
      (transverseCubicWeight i + transverseCubicWeight j) F) i j) =
        stationaryAxisTrace (hessian F i j)
    exact (stationaryAxisTrace_hessian_layer F i j).symm
  rw [he]
  change ((stationaryAxisTrace (K := K)).toRingHom.mapMatrix (hessian F)).det = _
  rw [← RingHom.map_det]
  change stationaryAxisTrace (hessianDeterminant F) = _
  rw [hdet]
  simp [stationaryAxisTrace, lineEval]

private theorem stationaryAxisTrace_quadratic_secant
    (P : _root_.Polynomial K) (hP : P.natDegree ≤ 2) :
    P.eval 1 - P.eval 0 = P.derivative.eval (1/2) := by
  have he : P = _root_.Polynomial.C (P.coeff 0) +
      _root_.Polynomial.C (P.coeff 1) * _root_.Polynomial.X +
      _root_.Polynomial.C (P.coeff 2) * _root_.Polynomial.X^2 := by
    apply _root_.Polynomial.ext
    intro n
    have hz (k : ℕ) : P.coeff (k+3) = 0 :=
      _root_.Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simp
      | succ n =>
        cases n with
        | zero => simp
        | succ n =>
          simpa [_root_.Polynomial.coeff_C_mul, _root_.Polynomial.coeff_X_pow,
            Nat.succ_eq_add_one, Nat.add_assoc] using hz n
  have h1 := congrArg (fun p : _root_.Polynomial K => p.eval 1) he
  have h0 := congrArg (fun p : _root_.Polynomial K => p.eval 0) he
  have hd := congrArg (fun p : _root_.Polynomial K => p.derivative.eval (1/2)) he
  dsimp only at h1 h0 hd
  rw [h1, h0, hd]
  simp [_root_.Polynomial.derivative_add, _root_.Polynomial.derivative_mul,
    _root_.Polynomial.derivative_pow] <;> ring

/-- Arbitrary total degree is allowed: a quadratic restriction of the
actual gradient to the marked axis is enough to forbid the collision. -/
theorem stationaryAxisTrace_quadraticGradient_markedCollision_impossible
    (F : StationarySource K) {δ : K} (hδ : δ ≠ 0)
    (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (hcoll : ∀ i : Unit ⊕ Fin 3,
      stationaryAxisEval 1 (pderiv i F) = stationaryAxisEval 0 (pderiv i F))
    (hquad : ∀ i : Unit ⊕ Fin 3,
      (stationaryAxisTrace (pderiv i F)).natDegree ≤ 2) : False := by
  classical
  have hz (i : Unit ⊕ Fin 3) :
      ((stationaryAxisTrace (pderiv i F)).derivative).eval (1/2) = 0 := by
    have he := stationaryAxisTrace_quadratic_secant
      (stationaryAxisTrace (pderiv i F)) (hquad i)
    rw [stationaryAxisTrace_eval, stationaryAxisTrace_eval, hcoll i, sub_self] at he
    exact he.symm
  have hb := stationaryAxisTrace_gradient_bezout F hdet
  let A := (stationaryAxisTrace (K := K)).toRingHom.mapMatrix (hessian F)
  change (∑ i : Unit ⊕ Fin 3,
    (stationaryAxisTrace (pderiv i F)).derivative * A.adjugate (.inl ()) i) =
      _root_.Polynomial.C δ at hb
  have he := congrArg (fun p : _root_.Polynomial K => p.eval (1/2)) hb
  change (_root_.Polynomial.evalRingHom (1/2 : K))
    (∑ i : Unit ⊕ Fin 3,
      (stationaryAxisTrace (pderiv i F)).derivative * A.adjugate (.inl ()) i) =
    (_root_.Polynomial.evalRingHom (1/2 : K)) (_root_.Polynomial.C δ) at he
  simp only [map_sum, map_mul, _root_.Polynomial.coe_evalRingHom,
    hz, zero_mul, Finset.sum_const_zero, _root_.Polynomial.eval_C] at he
  exact hδ he.symm

/-- Any surviving marked collision forces a genuinely higher-degree
gradient trace in transverse grade zero or one of the actual source.
Higher layers cannot conceal this necessary condition. -/
theorem stationaryAxisTrace_collision_forces_lowLayer_degree
    (F : StationarySource K) {δ : K} (hδ : δ ≠ 0)
    (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (hcoll : ∀ i : Unit ⊕ Fin 3,
      stationaryAxisEval 1 (pderiv i F) = stationaryAxisEval 0 (pderiv i F)) :
    ∃ i : Unit ⊕ Fin 3, 3 ≤ (stationaryAxisTrace
      (pderiv i (initialForm transverseCubicWeight
        (transverseCubicWeight i) F))).natDegree := by
  by_contra! h
  apply stationaryAxisTrace_quadraticGradient_markedCollision_impossible F hδ hdet hcoll
  intro i
  rw [stationaryAxisTrace_gradient_layer]
  have hi := h i
  omega




/-! ## Mixed-gap propagation to the actual terminal layers

A sufficiently late mixed correction forces every pre-gap
longitudinal correction to vanish, using the exact determinant
clock. The gap condition is explicit; it is not yet extracted
from the leading characteristic classification.
-/

section MixedGap

variable {R : Type*} [CommRing R] [IsDomain R]
local notation "RP" => _root_.Polynomial R

private theorem transverse_gap_mul
    (p q : RP) (a b n : ℕ) (hn : n < a+b)
    (hp : ∀ i < a, p.coeff i = 0)
    (hq : ∀ i < b, q.coeff i = 0) :
    (p*q).coeff n = 0 := by
  rw [_root_.Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hh := Finset.mem_antidiagonal.mp hij
  by_cases hi : ij.1 < a
  · rw [hp _ hi, zero_mul]
  · rw [hq _ (by omega), mul_zero]

private theorem transverse_gap_triple
    (p q r : RP) (k n : ℕ) (hn : n < 2*k)
    (hp : ∀ i < k, p.coeff i = 0)
    (hq : ∀ i < k, q.coeff i = 0) :
    (p*q*r).coeff n = 0 := by
  apply transverse_gap_mul (p*q) r (2*k) 0 n (by omega)
  · intro i hi
    exact transverse_gap_mul p q k k i (by omega) hp hq
  · intro i hi
    omega

/-- A mixed gap of length k implies a gap of length 2*k in the
quadratic adjugate pairing. -/
theorem transverseSchurMixed_coeff_zero_of_gap
    (H : GeneralFourBlock RP) (k n : ℕ) (hn : n < 2*k)
    (hb : ∀ i < k, H.b.coeff i = 0)
    (hp : ∀ i < k, H.p.coeff i = 0)
    (hq : ∀ i < k, H.q.coeff i = 0) :
    (transverseSchurMixed H).coeff n = 0 := by
  simp only [transverseSchurMixed, _root_.Polynomial.coeff_add,
    _root_.Polynomial.coeff_sub,
    transverse_gap_triple _ _ _ k n hn hb hb,
    transverse_gap_triple _ _ _ k n hn hb hp,
    transverse_gap_triple _ _ _ k n hn hb hq,
    transverse_gap_triple _ _ _ k n hn hp hp,
    transverse_gap_triple _ _ _ k n hn hp hq,
    transverse_gap_triple _ _ _ k n hn hq hq, sub_self, add_zero]

/-- The determinant and mixed gaps propagate through the cleared
Schur recurrence, with no inverse or division of coefficients. -/
theorem transverseSchur_longitudinal_zero_of_mixedGap
    (H : GeneralFourBlock RP) (k clock : ℕ)
    (hreg : (transverseSchurDet H).coeff 0 ≠ 0)
    (hb : ∀ i < k, H.b.coeff i = 0)
    (hp : ∀ i < k, H.p.coeff i = 0)
    (hq : ∀ i < k, H.q.coeff i = 0)
    (hdet : ∀ i < clock, H.determinantCore.coeff i = 0) :
    ∀ n < 2*k, n < clock → H.a.coeff n = 0 := by
  classical
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro hn hc
    have he := transverseSchur_coeff_recurrence H n
    have hsum : (∑ ij ∈ (Finset.antidiagonal n).erase (n, 0),
        H.a.coeff ij.1 * (transverseSchurDet H).coeff ij.2) = 0 := by
      apply Finset.sum_eq_zero
      intro ij hij
      have hh := Finset.mem_antidiagonal.mp (Finset.mem_of_mem_erase hij)
      have hne := Finset.ne_of_mem_erase hij
      have hi : ij.1 < n := by
        by_contra! h
        apply hne
        exact Prod.ext (by omega) (by omega)
      rw [ih ij.1 hi (by omega) (by omega), zero_mul]
    rw [hdet n hc, transverseSchurMixed_coeff_zero_of_gap H k n hn hb hp hq,
      hsum, zero_add, sub_zero] at he
    exact (mul_eq_zero.mp he).resolve_right hreg

end MixedGap

/-- In a genuine source characteristic chart, a mixed gap forces
actual source layers to be affine in characteristic time all the
way up to the smaller of twice the gap and the determinant clock. -/
theorem sourceLeading_correction_secondDerivative_zero_of_mixedGap
    {E : Type*} [CommRing E] [IsDomain E] [Algebra K E]
    (F : StationarySource K) (m k j : ℕ) (hm : 2 ≤ m) (hj : j ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E) (hV : V (.inl ()) = 1)
    (hreg : (transverseSchurDet (sourceLeading_lineSchurFrame F m z V)).coeff 0 ≠ 0)
    (hb : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).b.coeff i = 0)
    (hp : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).p.coeff i = 0)
    (hq : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).q.coeff i = 0)
    (hgap : j < 2*k) (hclock : j < 4*m-6) :
    (lineEval z V (initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F)).derivative.derivative = 0 := by
  let H := sourceLeading_lineSchurFrame F m z V
  have hd (i : ℕ) (hi : i < 4*m-6) : H.determinantCore.coeff i = 0 := by
    change (sourceLeading_lineSchurFrame F m z V).determinantCore.coeff i = 0
    rw [sourceLeading_lineSchurFrame_det F m hm hcap hdet,
      _root_.Polynomial.coeff_monomial, if_neg (by omega : 4*m-6 ≠ i)]
  have ha := transverseSchur_longitudinal_zero_of_mixedGap H k (4*m-6)
    hreg hb hp hq hd j hgap hclock
  rw [(sourceLeading_lineSchurFrame_differential_coeff F m j hj z V hV).1] at ha
  exact ha

/-- A mixed gap reaching beyond the bottom two source layers makes
both of them affine in the same actual characteristic chart. -/
theorem sourceLeading_bottomLayers_secondDerivative_zero_of_mixedGap
    {E : Type*} [CommRing E] [IsDomain E] [Algebra K E]
    (F : StationarySource K) (m k : ℕ) (hm : 3 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E) (hV : V (.inl ()) = 1)
    (hreg : (transverseSchurDet (sourceLeading_lineSchurFrame F m z V)).coeff 0 ≠ 0)
    (hb : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).b.coeff i = 0)
    (hp : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).p.coeff i = 0)
    (hq : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).q.coeff i = 0)
    (hgap : m < 2*k) :
    (lineEval z V (initialForm transverseCubicWeight 0 F)).derivative.derivative = 0 ∧
      (lineEval z V (initialForm transverseCubicWeight 1 F)).derivative.derivative = 0 := by
  have h0 := sourceLeading_correction_secondDerivative_zero_of_mixedGap
    F m k m (by omega) (by omega) hcap hdet z V hV hreg hb hp hq hgap (by omega)
  have h1 := sourceLeading_correction_secondDerivative_zero_of_mixedGap
    F m k (m-1) (by omega) (by omega) hcap hdet z V hV hreg hb hp hq (by omega) (by omega)
  constructor
  · simpa only [sub_self] using h0
  · have he : (m : ℤ) - ((m-1 : ℕ) : ℤ) = 1 := by omega
    rwa [he] at h1




/-! ## Close the late-mixed-gap branch on the actual marked axis -/

private def sourceAxisTimeEval (u : K) : LineTime K →+* K :=
  _root_.Polynomial.eval₂RingHom (MvPolynomial.eval (fun _ : Fin 3 => 0)) u

private theorem sourceAxisTimeEval_C (u : K) (b : MvPolynomial (Fin 3) K) :
    sourceAxisTimeEval u (_root_.Polynomial.C b) =
      MvPolynomial.eval (fun _ : Fin 3 => 0) b := by
  simp [sourceAxisTimeEval]

private theorem sourceAxisTimeEval_X (u : K) :
    sourceAxisTimeEval u (_root_.Polynomial.X : LineTime K) = u := by
  simp [sourceAxisTimeEval]

private theorem sourceReferenceLinearVector_eval_zero
    (N : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    MvPolynomial.eval (fun _ : Fin 3 => 0) (referenceLinearVector N i) = 0 := by
  simp [referenceLinearVector]

/-- The linear characteristic chart restricts on the marked axis
to the honest translation x = a+u. -/
private theorem sourceAxisTimeEval_linearLineEval
    (a u : K) (N : Matrix (Fin 3) (Fin 3) K) (P : StationarySource K) :
    sourceAxisTimeEval u (linearLineEval a N P) = stationaryAxisEval (a+u) P := by
  induction P using MvPolynomial.induction_on with
  | C c =>
    have h : linearLineEval a N (MvPolynomial.C c) =
        _root_.Polynomial.C (MvPolynomial.C c) := by simp [linearLineEval, lineEval]
    rw [h, sourceAxisTimeEval_C]
    simp [stationaryAxisEval]
  | add p q hp hq =>
    simp only [map_add, hp, hq]
  | mul_X p i hp =>
    rw [map_mul, map_mul, map_mul, hp]
    congr 1
    cases i with
    | inl v =>
      cases v
      have h : linearLineEval a N (X (.inl ())) =
          _root_.Polynomial.C (MvPolynomial.C a : MvPolynomial (Fin 3) K) +
            _root_.Polynomial.X := by simp [linearLineEval, lineEval]
      rw [h, map_add, sourceAxisTimeEval_C, sourceAxisTimeEval_X]
      simp [stationaryAxisEval]
    | inr i =>
      have h : linearLineEval a N (X (.inr i)) =
          _root_.Polynomial.C (X i : MvPolynomial (Fin 3) K) +
            _root_.Polynomial.C (referenceLinearVector N i) * _root_.Polynomial.X := by
        simp [linearLineEval, lineEval, referenceLinearVector]
      rw [h, map_add, map_mul, sourceAxisTimeEval_C, sourceAxisTimeEval_C,
        sourceAxisTimeEval_X, sourceReferenceLinearVector_eval_zero]
      simp [stationaryAxisEval]

private theorem sourceAxisTimeEval_linearLineEval_derivative
    (a u : K) (N : Matrix (Fin 3) (Fin 3) K) (P : StationarySource K) :
    sourceAxisTimeEval u (linearLineEval a N P).derivative =
      stationaryAxisEval (a+u) (pderiv (.inl ()) P) := by
  classical
  let z : Unit ⊕ Fin 3 → MvPolynomial (Fin 3) K :=
    Sum.elim (fun _ => MvPolynomial.C a) X
  let V : Unit ⊕ Fin 3 → MvPolynomial (Fin 3) K :=
    Sum.elim (fun _ => 1) (referenceLinearVector N)
  change sourceAxisTimeEval u (lineEval z V P).derivative = _
  rw [transverse_lineEval_derivative, map_sum, Fintype.sum_sum_type]
  have he (i : Unit ⊕ Fin 3) : sourceAxisTimeEval u
      (_root_.Polynomial.C (V i) * lineEval z V (pderiv i P)) =
      MvPolynomial.eval (fun _ : Fin 3 => 0) (V i) *
        stationaryAxisEval (a+u) (pderiv i P) := by
    rw [map_mul, sourceAxisTimeEval_C]
    exact congrArg (fun c => MvPolynomial.eval (fun _ : Fin 3 => 0) (V i) * c)
      (sourceAxisTimeEval_linearLineEval a u N (pderiv i P))
  simp_rw [he]
  simp [V, referenceLinearVector]

private theorem sourceTime_degree_le_one_of_second_zero
    (P : LineTime K) (hP : P.derivative.derivative = 0) : P.natDegree ≤ 1 := by
  have hd := _root_.Polynomial.eq_C_of_derivative_eq_zero hP
  let c := P.derivative.coeff 0
  have hzero : (P - _root_.Polynomial.C c * _root_.Polynomial.X).derivative = 0 := by
    rw [map_sub, _root_.Polynomial.derivative_C_mul_X, hd]
    exact sub_self _
  have he := _root_.Polynomial.eq_C_of_derivative_eq_zero hzero
  have hp : P = _root_.Polynomial.C ((P - _root_.Polynomial.C c *
      _root_.Polynomial.X).coeff 0) + _root_.Polynomial.C c * _root_.Polynomial.X := by
    calc
      P = (P - _root_.Polynomial.C c * _root_.Polynomial.X) +
          _root_.Polynomial.C c * _root_.Polynomial.X := by ring
      _ = _ := congrArg (fun q : LineTime K => q + _root_.Polynomial.C c *
        _root_.Polynomial.X) he
  rw [hp]
  exact _root_.Polynomial.natDegree_add_le_of_degree_le (by simp)
    ((_root_.Polynomial.natDegree_C_mul_le _ _).trans (by simp))

private theorem sourceAxisTimeEval_affine_formula
    (P : LineTime K) (hP : P.natDegree ≤ 1) (u : K) :
    sourceAxisTimeEval u P =
      MvPolynomial.eval (fun _ : Fin 3 => 0) (P.coeff 0) +
        MvPolynomial.eval (fun _ : Fin 3 => 0) (P.coeff 1) * u := by
  have he : P = _root_.Polynomial.C (P.coeff 0) +
      _root_.Polynomial.C (P.coeff 1) * _root_.Polynomial.X := by
    apply _root_.Polynomial.ext
    intro n
    cases n with
    | zero => simp
    | succ n =>
      cases n with
      | zero => simp
      | succ n =>
        have hz : P.coeff (n+2) = 0 :=
          _root_.Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
        simpa [_root_.Polynomial.coeff_C_mul_X, Nat.succ_eq_add_one,
          Nat.add_assoc] using hz
  calc
    _ = sourceAxisTimeEval u (_root_.Polynomial.C (P.coeff 0) +
        _root_.Polynomial.C (P.coeff 1) * _root_.Polynomial.X) :=
      congrArg (sourceAxisTimeEval u) he
    _ = _ := by rw [map_add, map_mul, sourceAxisTimeEval_C,
      sourceAxisTimeEval_C, sourceAxisTimeEval_X]

private theorem sourceAxisTimeEval_affine_eq_of_endpoints
    (P Q : LineTime K) (hp : P.natDegree ≤ 1) (hq : Q.natDegree ≤ 1)
    (a : K)
    (h0 : sourceAxisTimeEval (-a) P = sourceAxisTimeEval (-a) Q)
    (h1 : sourceAxisTimeEval (1-a) P = sourceAxisTimeEval (1-a) Q) (u : K) :
    sourceAxisTimeEval u P = sourceAxisTimeEval u Q := by
  rw [sourceAxisTimeEval_affine_formula P hp, sourceAxisTimeEval_affine_formula Q hq] at h0 h1 ⊢
  have hs : MvPolynomial.eval (fun _ : Fin 3 => 0) (P.coeff 1) =
      MvPolynomial.eval (fun _ : Fin 3 => 0) (Q.coeff 1) := by
    linear_combination h1 - h0
  rw [hs] at h0 ⊢
  have hc : MvPolynomial.eval (fun _ : Fin 3 => 0) (P.coeff 0) =
      MvPolynomial.eval (fun _ : Fin 3 => 0) (Q.coeff 0) := by
    linear_combination h0
  rw [hc]

private theorem stationaryAxisEval_gradient_layer
    (F : StationarySource K) (i : Unit ⊕ Fin 3) (t : K) :
    stationaryAxisEval t (pderiv i F) =
      stationaryAxisEval t (pderiv i (initialForm transverseCubicWeight
        (transverseCubicWeight i) F)) := by
  have h := congrArg (fun p : _root_.Polynomial K => p.eval t)
    (stationaryAxisTrace_gradient_layer F i)
  simpa only [stationaryAxisTrace_eval] using h

/-- Affineness of the transverse-degree-one layer alone excludes a
marked collision. The pencil interpolation makes the actual transverse
gradient constant, and the rank-one axis obstruction handles the
longitudinal gradient without any hypothesis on its degree. -/
theorem sourceNilpotent_affineLinearLayer_markedCollision_impossible
    (F : StationarySource K) {δ : K} (hδ : δ ≠ 0)
    (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (hcoll : ∀ i : Unit ⊕ Fin 3,
      stationaryAxisEval 1 (pderiv i F) = stationaryAxisEval 0 (pderiv i F))
    (h1 : (linearLineEval a N (initialForm transverseCubicWeight 1 F)).derivative.derivative = 0) :
    False := by
  classical
  let Q1 := initialForm transverseCubicWeight 1 F
  let P1 := linearLineEval a N Q1
  let G (u : K) (i : Fin 3) := stationaryAxisEval (a+u) (pderiv (.inr i) Q1)
  let c := G (-a)
  let J (u : K) := (sourceTimePencil N).map (sourceAxisTimeEval u)
  let D (j : Fin 3) := coeffDeriv (pderiv j) P1
  let R (j : Fin 3) := ∑ i : Fin 3,
    _root_.Polynomial.C (MvPolynomial.C (c i)) * sourceTimePencil N i j
  have hdegD (j : Fin 3) : (D j).natDegree ≤ 1 :=
    (sourceTime_coeffDeriv_natDegree_le (pderiv j) P1).trans
      (sourceTime_degree_le_one_of_second_zero P1 h1)
  have hdegR (j : Fin 3) : (R j).natDegree ≤ 1 := by
    apply sourceTime_natDegree_sum_le
    intro i _
    exact (_root_.Polynomial.natDegree_C_mul_le _ _).trans
      (sourceTimePencil_natDegree_le N i j)
  have hchain (u : K) : G u ᵥ* J u = fun j => sourceAxisTimeEval u (D j) := by
    funext j
    have h := congrArg (fun v : Fin 3 → LineTime K => sourceAxisTimeEval u (v j))
      (sourceLinear_referenceGradient_chain a N Q1)
    change sourceAxisTimeEval u (∑ i : Fin 3,
      linearLineEval a N (pderiv (.inr i) Q1) * sourceTimePencil N i j) =
        sourceAxisTimeEval u (D j) at h
    rw [map_sum] at h
    simp only [map_mul, sourceAxisTimeEval_linearLineEval] at h
    exact h
  have hconst (u : K) : c ᵥ* J u = fun j => sourceAxisTimeEval u (R j) := by
    funext j
    change (∑ i : Fin 3, c i * sourceAxisTimeEval u (sourceTimePencil N i j)) =
      sourceAxisTimeEval u (∑ i : Fin 3,
        _root_.Polynomial.C (MvPolynomial.C (c i)) * sourceTimePencil N i j)
    rw [map_sum]
    simp only [map_mul, sourceAxisTimeEval_C, MvPolynomial.eval_C]
  have hG1 : G (1-a) = c := by
    funext i
    change stationaryAxisEval (a+(1-a)) (pderiv (.inr i) Q1) =
      stationaryAxisEval (a+(-a)) (pderiv (.inr i) Q1)
    rw [show a+(1-a) = 1 by ring, add_neg_cancel]
    have hl (t : K) : stationaryAxisEval t (pderiv (.inr i) F) =
        stationaryAxisEval t (pderiv (.inr i) Q1) :=
      stationaryAxisEval_gradient_layer F (.inr i) t
    rw [← hl 1, ← hl 0]
    exact hcoll (.inr i)
  have hendpoint (u : K) (hu : G u = c) (j : Fin 3) :
      sourceAxisTimeEval u (D j) = sourceAxisTimeEval u (R j) := by
    calc
      _ = (G u ᵥ* J u) j := (congrFun (hchain u) j).symm
      _ = (c ᵥ* J u) j := by rw [hu]
      _ = _ := congrFun (hconst u) j
  have hG (u : K) : G u = c := by
    have he : G u ᵥ* J u = c ᵥ* J u := by
      rw [hchain u, hconst u]
      funext j
      exact sourceAxisTimeEval_affine_eq_of_endpoints (D j) (R j)
        (hdegD j) (hdegR j) a (hendpoint (-a) rfl j)
        (hendpoint (1-a) hG1 j) u
    let S := (sourceTimePencilInv N).map (sourceAxisTimeEval u)
    have hinv : J u * S = 1 := by
      change (sourceTimePencil N).map (sourceAxisTimeEval u) *
        (sourceTimePencilInv N).map (sourceAxisTimeEval u) = _
      rw [← Matrix.map_mul, sourceTimePencil_right_inverse N hN]
      apply Matrix.ext
      intro i j
      simp [Matrix.map_apply, Matrix.one_apply]
    calc
      G u = G u ᵥ* (1 : Matrix (Fin 3) (Fin 3) K) := (Matrix.vecMul_one _).symm
      _ = G u ᵥ* (J u * S) := by rw [hinv]
      _ = (G u ᵥ* J u) ᵥ* S := (Matrix.vecMul_vecMul _ _ _).symm
      _ = (c ᵥ* J u) ᵥ* S := by rw [he]
      _ = c := by rw [Matrix.vecMul_vecMul, hinv, Matrix.vecMul_one]
  let D0 := (stationaryAxisTrace (pderiv (.inl ()) F)).derivative
  apply stationaryAxisTrace_rankOne_markedCollision_impossible F hδ hdet hcoll
    D0 (Sum.elim (fun _ : Unit => 1) (fun _ : Fin 3 => 0))
  intro i
  cases i with
  | inl v =>
    cases v
    change D0 = _root_.Polynomial.C (1 : K) * D0
    simp
  | inr i =>
    have hall (t : K) : stationaryAxisEval t (pderiv (.inr i) F) =
        stationaryAxisEval 0 (pderiv (.inr i) F) := by
      rw [stationaryAxisEval_gradient_layer F (.inr i) t,
        stationaryAxisEval_gradient_layer F (.inr i) 0]
      have h := congrFun (hG (t-a)) i
      change stationaryAxisEval (a+(t-a)) (pderiv (.inr i) Q1) =
        stationaryAxisEval (a+(-a)) (pderiv (.inr i) Q1) at h
      rw [show a+(t-a) = t by ring, add_neg_cancel] at h
      exact h
    have he : stationaryAxisTrace (pderiv (.inr i) F) =
        _root_.Polynomial.C (stationaryAxisEval 0 (pderiv (.inr i) F)) := by
      apply _root_.Polynomial.funext
      intro t
      rw [stationaryAxisTrace_eval, _root_.Polynomial.eval_C]
      exact hall t
    change (stationaryAxisTrace (pderiv (.inr i) F)).derivative =
      _root_.Polynomial.C (0 : K) * D0
    rw [he, _root_.Polynomial.derivative_C, map_zero, zero_mul]

/-- Affineness of both bottom source layers in a nilpotent
characteristic chart excludes an actual marked gradient collision.
The affine pencil is used on the original gradient, not on a
replacement Hessian determinant. -/
theorem sourceNilpotent_affineBottomLayers_markedCollision_impossible
    (F : StationarySource K) {δ : K} (hδ : δ ≠ 0)
    (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (hcoll : ∀ i : Unit ⊕ Fin 3,
      stationaryAxisEval 1 (pderiv i F) = stationaryAxisEval 0 (pderiv i F))
    (h0 : (linearLineEval a N (initialForm transverseCubicWeight 0 F)).derivative.derivative = 0)
    (h1 : (linearLineEval a N (initialForm transverseCubicWeight 1 F)).derivative.derivative = 0) :
    False := by
  exact sourceNilpotent_affineLinearLayer_markedCollision_impossible
    F hδ hdet a N hN hcoll h1

/-- The mixed block of a surviving regular nilpotent-linear marked
collision must have a nonzero correction by reverse order floor((m-1)/2).
The order-zero block is excluded by the actual leading transport. -/
theorem sourceNilpotent_markedCollision_forces_strictEarlyMixed
    (F : StationarySource K) (m : ℕ) (hm : 3 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hδ : δ ≠ 0) (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (hreg : referenceSlice a
      ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)) =
        _root_.Polynomial.C (referenceSlice a
          (pderiv i (initialForm transverseCubicWeight (m : ℤ) F))))
    (hcoll : ∀ i : Unit ⊕ Fin 3,
      stationaryAxisEval 1 (pderiv i F) = stationaryAxisEval 0 (pderiv i F)) :
    let B := MvPolynomial (Fin 3) K
    let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
    let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
    let H := sourceLeading_lineSchurFrame F m z V
    ∃ j : ℕ, 0 < j ∧ 2*j < m ∧
      (H.b.coeff j ≠ 0 ∨ H.p.coeff j ≠ 0 ∨ H.q.coeff j ≠ 0) := by
  let B := MvPolynomial (Fin 3) K
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
  let H := sourceLeading_lineSchurFrame F m z V
  let L := initialForm transverseCubicWeight (m : ℤ) F
  have hV : V (.inl ()) = 1 := rfl
  have hz : MvPolynomial.aeval z ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0 := hreg
  have hg : ∀ i, lineEval z V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval z (pderiv i L)) := hgrad
  obtain ⟨hb0, hp0, hq0, hr⟩ :=
    sourceLeading_lineSchurFrame_kernel_regular F m z V hV hz hg
  change ∃ j : ℕ, 0 < j ∧ 2*j < m ∧
    (H.b.coeff j ≠ 0 ∨ H.p.coeff j ≠ 0 ∨ H.q.coeff j ≠ 0)
  by_contra hn
  let k := (m-1)/2+1
  have hgap : m-1 < 2*k := by dsimp [k]; omega
  have hzero (j : ℕ) (hj : j < k) :
      H.b.coeff j = 0 ∧ H.p.coeff j = 0 ∧ H.q.coeff j = 0 := by
    by_cases hj0 : j = 0
    · subst j
      exact ⟨hb0, hp0, hq0⟩
    · have hjm : 2*j < m := by dsimp [k] at hj; omega
      have hjpos : 0 < j := by omega
      refine ⟨?_, ?_, ?_⟩
      · by_contra h
        exact hn ⟨j, hjpos, hjm, Or.inl h⟩
      · by_contra h
        exact hn ⟨j, hjpos, hjm, Or.inr (Or.inl h)⟩
      · by_contra h
        exact hn ⟨j, hjpos, hjm, Or.inr (Or.inr h)⟩
  have h1 := sourceLeading_correction_secondDerivative_zero_of_mixedGap
    F m k (m-1) (by omega) (by omega) hcap hdet z V hV hr
    (fun j hj => (hzero j hj).1) (fun j hj => (hzero j hj).2.1)
    (fun j hj => (hzero j hj).2.2) hgap (by omega)
  have he : (m : ℤ) - ((m-1 : ℕ) : ℤ) = 1 := by omega
  rw [he] at h1
  exact sourceNilpotent_affineLinearLayer_markedCollision_impossible
    F hδ hdet a N hN hcoll h1


/-- The mixed block of a surviving regular nilpotent-linear marked
collision must have a nonzero correction by reverse order floor(m/2).
The order-zero block is excluded by the actual leading transport. -/
theorem sourceNilpotent_markedCollision_forces_earlyMixed
    (F : StationarySource K) (m : ℕ) (hm : 3 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hδ : δ ≠ 0) (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (hreg : referenceSlice a
      ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)) =
        _root_.Polynomial.C (referenceSlice a
          (pderiv i (initialForm transverseCubicWeight (m : ℤ) F))))
    (hcoll : ∀ i : Unit ⊕ Fin 3,
      stationaryAxisEval 1 (pderiv i F) = stationaryAxisEval 0 (pderiv i F)) :
    let B := MvPolynomial (Fin 3) K
    let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
    let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
    let H := sourceLeading_lineSchurFrame F m z V
    ∃ j : ℕ, 0 < j ∧ 2*j ≤ m ∧
      (H.b.coeff j ≠ 0 ∨ H.p.coeff j ≠ 0 ∨ H.q.coeff j ≠ 0) := by
  obtain ⟨j, hj, hjm, hmix⟩ :=
    sourceNilpotent_markedCollision_forces_strictEarlyMixed F m hm hcap hδ hdet
      a N hN hreg hgrad hcoll
  exact ⟨j, hj, hjm.le, hmix⟩




/-! ## First mixed-gap endpoint: exact polynomial divisibility

Unlike the pre-endpoint vanishing, the endpoint retains the actual
quadratic mixed correction. This isolates the divisibility constraint
at any first mixed order, not just order one.
-/

section MixedGapEndpoint

variable {R : Type*} [CommRing R] [IsDomain R]
local notation "RP" => _root_.Polynomial R

private theorem transverse_gap_mul_endpoint
    (p q : RP) (a b : ℕ)
    (hp : ∀ i < a, p.coeff i = 0)
    (hq : ∀ i < b, q.coeff i = 0) :
    (p*q).coeff (a+b) = p.coeff a * q.coeff b := by
  classical
  rw [_root_.Polynomial.coeff_mul, Finset.sum_eq_single (a,b)]
  · intro ij hij hne
    have hh := Finset.mem_antidiagonal.mp hij
    by_cases hi : ij.1 < a
    · rw [hp _ hi, zero_mul]
    · have hj : ij.2 < b := by
        by_contra! hj
        apply hne
        exact Prod.ext (by omega) (by omega)
      rw [hq _ hj, mul_zero]
  · intro h
    exact (h (Finset.mem_antidiagonal.mpr rfl)).elim

private theorem transverse_gap_triple_endpoint
    (p q r : RP) (k : ℕ)
    (hp : ∀ i < k, p.coeff i = 0)
    (hq : ∀ i < k, q.coeff i = 0) :
    (p*q*r).coeff (2*k) = p.coeff k * q.coeff k * r.coeff 0 := by
  have hpq : ∀ i < k+k, (p*q).coeff i = 0 :=
    fun i hi => transverse_gap_mul p q k k i hi hp hq
  have hr : ∀ i < (0 : ℕ), r.coeff i = 0 := by
    intro i hi
    omega
  have he := transverse_gap_mul_endpoint (p*q) r (k+k) 0 hpq hr
  rw [transverse_gap_mul_endpoint p q k k hp hq] at he
  simpa only [add_zero, two_mul] using he

/-- The first possible mixed pairing uses precisely two copies of
the gap-endpoint mixed row and the leading transverse block. -/
theorem transverseSchurMixed_coeff_gap_endpoint
    (H : GeneralFourBlock RP) (k : ℕ)
    (hb : ∀ i < k, H.b.coeff i = 0)
    (hp : ∀ i < k, H.p.coeff i = 0)
    (hq : ∀ i < k, H.q.coeff i = 0) :
    (transverseSchurMixed H).coeff (2*k) =
      transverseSchurMixed
        ({ a := 0, b := H.b.coeff k, p := H.p.coeff k,
           q := H.q.coeff k, d := H.d.coeff 0, r := H.r.coeff 0,
           s := H.s.coeff 0, x := H.x.coeff 0, y := H.y.coeff 0,
           z := H.z.coeff 0 } : GeneralFourBlock R) := by
  simp only [transverseSchurMixed, _root_.Polynomial.coeff_add,
    _root_.Polynomial.coeff_sub,
    transverse_gap_triple_endpoint _ _ _ k hb hb,
    transverse_gap_triple_endpoint _ _ _ k hb hp,
    transverse_gap_triple_endpoint _ _ _ k hb hq,
    transverse_gap_triple_endpoint _ _ _ k hp hp,
    transverse_gap_triple_endpoint _ _ _ k hp hq,
    transverse_gap_triple_endpoint _ _ _ k hq hq,
    _root_.Polynomial.mul_coeff_zero]

/-- The cleared Schur recurrence at twice the first mixed order.
The actual leading determinant divides the quadratic pairing. -/
theorem transverseSchur_mixedGap_endpoint
    (H : GeneralFourBlock RP) (k clock : ℕ) (hc : 2*k < clock)
    (hreg : (transverseSchurDet H).coeff 0 ≠ 0)
    (hb : ∀ i < k, H.b.coeff i = 0)
    (hp : ∀ i < k, H.p.coeff i = 0)
    (hq : ∀ i < k, H.q.coeff i = 0)
    (hdet : ∀ i < clock, H.determinantCore.coeff i = 0) :
    H.a.coeff (2*k) * (transverseSchurDet H).coeff 0 =
      transverseSchurMixed
        ({ a := 0, b := H.b.coeff k, p := H.p.coeff k,
           q := H.q.coeff k, d := H.d.coeff 0, r := H.r.coeff 0,
           s := H.s.coeff 0, x := H.x.coeff 0, y := H.y.coeff 0,
           z := H.z.coeff 0 } : GeneralFourBlock R) := by
  classical
  have ha := transverseSchur_longitudinal_zero_of_mixedGap H k clock
    hreg hb hp hq hdet
  have hsum : (∑ ij ∈ (Finset.antidiagonal (2*k)).erase (2*k,0),
      H.a.coeff ij.1 * (transverseSchurDet H).coeff ij.2) = 0 := by
    apply Finset.sum_eq_zero
    intro ij hij
    have hh := Finset.mem_antidiagonal.mp (Finset.mem_of_mem_erase hij)
    have hne := Finset.ne_of_mem_erase hij
    have hi : ij.1 < 2*k := by
      by_contra! h
      apply hne
      exact Prod.ext (by omega) (by omega)
    rw [ha _ hi (by omega), zero_mul]
  have he := transverseSchur_coeff_recurrence H (2*k)
  rw [hdet _ hc, transverseSchurMixed_coeff_gap_endpoint H k hb hp hq,
    hsum, zero_add, sub_zero] at he
  exact he

end MixedGapEndpoint

/-- Actual source endpoint identity at an arbitrary mixed gap. -/
theorem sourceLeading_mixedGap_endpoint_lineODE
    {E : Type*} [CommRing E] [IsDomain E] [Algebra K E]
    (F : StationarySource K) (m k : ℕ) (hm : 2 ≤ m)
    (hk : 2*k ≤ m) (hc : 2*k < 4*m-6)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E) (hV : V (.inl ()) = 1)
    (hreg : (transverseSchurDet (sourceLeading_lineSchurFrame F m z V)).coeff 0 ≠ 0)
    (hb : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).b.coeff i = 0)
    (hp : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).p.coeff i = 0)
    (hq : ∀ i < k, (sourceLeading_lineSchurFrame F m z V).q.coeff i = 0) :
    let H := sourceLeading_lineSchurFrame F m z V
    let Q := initialForm transverseCubicWeight ((m : ℤ)-((2*k : ℕ) : ℤ)) F
    (lineEval z V Q).derivative.derivative * (transverseSchurDet H).coeff 0 =
      transverseSchurMixed
        ({ a := 0, b := H.b.coeff k, p := H.p.coeff k,
           q := H.q.coeff k, d := H.d.coeff 0, r := H.r.coeff 0,
           s := H.s.coeff 0, x := H.x.coeff 0, y := H.y.coeff 0,
           z := H.z.coeff 0 } : GeneralFourBlock (_root_.Polynomial E)) := by
  let H := sourceLeading_lineSchurFrame F m z V
  have hd (i : ℕ) (hi : i < 4*m-6) : H.determinantCore.coeff i = 0 := by
    change (sourceLeading_lineSchurFrame F m z V).determinantCore.coeff i = 0
    rw [sourceLeading_lineSchurFrame_det F m hm hcap hdet,
      _root_.Polynomial.coeff_monomial, if_neg (by omega : 4*m-6 ≠ i)]
  have he := transverseSchur_mixedGap_endpoint H k (4*m-6) hc hreg hb hp hq hd
  rw [(sourceLeading_lineSchurFrame_differential_coeff F m (2*k) hk z V hV).1] at he
  exact he

/-- If twice the first mixed order reaches precisely the linear
transverse layer, the endpoint pairing cannot be isotropic in a
marked collision. This includes the regular nilpotent-linear cubic
branch with k = 1. -/
theorem sourceNilpotent_linearLayer_mixedGap_pairing_ne_zero
    (F : StationarySource K) (m k : ℕ) (hm : 3 ≤ m)
    (hk : 2*k+1 = m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hδ : δ ≠ 0) (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (hcoll : ∀ i : Unit ⊕ Fin 3,
      stationaryAxisEval 1 (pderiv i F) = stationaryAxisEval 0 (pderiv i F))
    (hreg : referenceSlice a
      ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)) =
        _root_.Polynomial.C (referenceSlice a
          (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)))) :
    let B := MvPolynomial (Fin 3) K
    let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
    let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
    let H := sourceLeading_lineSchurFrame F m z V
    (∀ i < k, H.b.coeff i = 0) →
    (∀ i < k, H.p.coeff i = 0) →
    (∀ i < k, H.q.coeff i = 0) →
    transverseSchurMixed
      ({ a := 0, b := H.b.coeff k, p := H.p.coeff k,
         q := H.q.coeff k, d := H.d.coeff 0, r := H.r.coeff 0,
         s := H.s.coeff 0, x := H.x.coeff 0, y := H.y.coeff 0,
         z := H.z.coeff 0 } : GeneralFourBlock (LineTime K)) ≠ 0 := by
  let B := MvPolynomial (Fin 3) K
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
  let H := sourceLeading_lineSchurFrame F m z V
  let L := initialForm transverseCubicWeight (m : ℤ) F
  have hV : V (.inl ()) = 1 := rfl
  have hz : MvPolynomial.aeval z ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0 := hreg
  have hg : ∀ i, lineEval z V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval z (pderiv i L)) := hgrad
  have hr := (sourceLeading_lineSchurFrame_kernel_regular F m z V hV hz hg).2.2.2
  change (∀ i < k, H.b.coeff i = 0) →
    (∀ i < k, H.p.coeff i = 0) →
    (∀ i < k, H.q.coeff i = 0) →
    transverseSchurMixed
      ({ a := 0, b := H.b.coeff k, p := H.p.coeff k,
         q := H.q.coeff k, d := H.d.coeff 0, r := H.r.coeff 0,
         s := H.s.coeff 0, x := H.x.coeff 0, y := H.y.coeff 0,
         z := H.z.coeff 0 } : GeneralFourBlock (LineTime K)) ≠ 0
  intro hb hp hq hzero
  have he := sourceLeading_mixedGap_endpoint_lineODE F m k (by omega)
    (by omega) (by omega) hcap hdet z V hV hr hb hp hq
  have hw : (m : ℤ) - ((2*k : ℕ) : ℤ) = 1 := by omega
  dsimp only at he
  rw [hw, hzero] at he
  have h1 := (mul_eq_zero.mp he).resolve_right hr
  exact sourceNilpotent_affineLinearLayer_markedCollision_impossible
    F hδ hdet a N hN hcoll h1

end
end HC4.Polynomial.RankThreeCubic
