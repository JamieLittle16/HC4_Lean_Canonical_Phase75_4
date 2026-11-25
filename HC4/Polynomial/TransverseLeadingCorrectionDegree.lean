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

/-!
# Higher transverse correction frames and degree bounds

Exact reverse-Rees characteristic frames, the second correction, nilpotent
characteristic-time degree bounds, uniform cleared Schur induction and
return to original source coordinates. Shared helpers used by subsequent
collision and mixed-pole arguments retain their existing statements.
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

/-! ## Actual second lower layer on the characteristic

The two parameters remain distinct: s is the reverse transverse Rees
parameter and t is time on the characteristic. The determinant clock
is in s, while every coefficient is a polynomial in t.
-/

def sourceLineIndex : Fin 4 ≃ Unit ⊕ Fin 3 where
  toFun := ![Sum.inl (), Sum.inr 0, Sum.inr 1, Sum.inr 2]
  invFun := Sum.elim (fun _ => 0) Fin.succ
  left_inv := by intro i; fin_cases i <;> rfl
  right_inv := by
    intro i
    cases i with
    | inl u => cases u; rfl
    | inr j => fin_cases j <;> rfl

def sourceLineBlockOfMatrix {R : Type*} [CommRing R]
    (M : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R) : GeneralFourBlock R :=
  GeneralFourBlock.ofSymmetricMatrix (M.submatrix sourceLineIndex sourceLineIndex)

theorem sourceLineBlockOfMatrix_det {R : Type*} [CommRing R]
    (M : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R)
    (hsym : ∀ i j, M i j = M j i) :
    (sourceLineBlockOfMatrix M).determinantCore = M.det := by
  rw [← GeneralFourBlock.matrix_det]
  unfold sourceLineBlockOfMatrix
  rw [GeneralFourBlock.matrix_ofSymmetricMatrix]
  · exact Matrix.det_submatrix_equiv_self sourceLineIndex M
  · intro i j
    exact hsym _ _

/-- Coefficientwise projection of the actual ten entries; this is not
a ring homomorphism on the determinant. -/
def transverseBlockCoeff {R : Type*} [CommRing R]
    (H : GeneralFourBlock (_root_.Polynomial R)) (j : ℕ) :
    GeneralFourBlock R where
  a := H.a.coeff j
  b := H.b.coeff j
  d := H.d.coeff j
  p := H.p.coeff j
  q := H.q.coeff j
  r := H.r.coeff j
  s := H.s.coeff j
  x := H.x.coeff j
  y := H.y.coeff j
  z := H.z.coeff j

/-- A constant-in-Rees-time characteristic frame commutes with taking
individual Rees coefficients. The entries may depend on line time. -/
theorem transverseCharacteristicFrame_coeff {R : Type*} [CommRing R]
    (H : GeneralFourBlock (_root_.Polynomial R)) (u v w : R) (j : ℕ) :
    transverseBlockCoeff (transverseCharacteristicFrame H
      (_root_.Polynomial.C u) (_root_.Polynomial.C v) (_root_.Polynomial.C w)) j =
      transverseCharacteristicFrame (transverseBlockCoeff H j) u v w := by
  apply GeneralFourBlock.ext <;>
    simp only [transverseBlockCoeff, transverseCharacteristicFrame,
      two_mul, add_mul, pow_two, ← _root_.Polynomial.C_mul,
      _root_.Polynomial.coeff_add, _root_.Polynomial.coeff_C_mul]

/-- The actual unframed reverse Hessian, evaluated along an affine
characteristic. Its coefficients lie in the line-time polynomial ring. -/
def sourceLeading_lineBlock
    {E : Type*} [CommRing E] [Algebra K E]
    (F : StationarySource K) (m : ℕ) (z V : Unit ⊕ Fin 3 → E) :
    GeneralFourBlock (_root_.Polynomial (_root_.Polynomial E)) :=
  sourceLineBlockOfMatrix
    ((_root_.Polynomial.mapRingHom (lineEval z V).toRingHom).mapMatrix
      (sourceLeading_reverseHessian F m))

theorem sourceLeading_lineBlock_det
    {E : Type*} [CommRing E] [Algebra K E]
    (F : StationarySource K) (m : ℕ) (hm : 2 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E) :
    (sourceLeading_lineBlock F m z V).determinantCore =
      _root_.Polynomial.monomial (4*m-6)
        (lineEval z V (MvPolynomial.C δ)) := by
  let φ : _root_.Polynomial (StationarySource K) →+*
      _root_.Polynomial (_root_.Polynomial E) :=
    _root_.Polynomial.mapRingHom (lineEval (K := K) z V).toRingHom
  have hsym (i j : Unit ⊕ Fin 3) :
      sourceLeading_reverseHessian F m i j =
        sourceLeading_reverseHessian F m j i := by
    apply _root_.Polynomial.ext
    intro k
    rw [sourceLeading_reverseHessian_coeff, sourceLeading_reverseHessian_coeff]
    split_ifs
    · simp only [hessian_apply, HC4.Newton.pderiv_comm_backport j i]
    · rfl
  change (sourceLineBlockOfMatrix (φ.mapMatrix
    (sourceLeading_reverseHessian F m))).determinantCore = _
  rw [sourceLineBlockOfMatrix_det, ← RingHom.map_det,
    sourceLeading_reverseHessian_constantDet F m hm hcap hdet]
  · exact _root_.Polynomial.map_monomial (lineEval (K := K) z V).toRingHom
  · intro i j
    change φ (sourceLeading_reverseHessian F m i j) =
      φ (sourceLeading_reverseHessian F m j i)
    rw [hsym]

/-- The coefficient at j is literally the evaluated Hessian of the
jth lower source layer. No new potential is introduced. -/
theorem sourceLeading_lineBlock_coeff
    {E : Type*} [CommRing E] [Algebra K E]
    (F : StationarySource K) (m j : ℕ) (hj : j ≤ m)
    (z V : Unit ⊕ Fin 3 → E) :
    transverseBlockCoeff (sourceLeading_lineBlock F m z V) j =
      sourceLineBlockOfMatrix ((lineEval z V).toRingHom.mapMatrix
        (hessian (initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F))) := by
  apply GeneralFourBlock.ext <;>
    simp only [transverseBlockCoeff, sourceLeading_lineBlock, sourceLineBlockOfMatrix,
      GeneralFourBlock.ofSymmetricMatrix, Matrix.submatrix_apply, RingHom.mapMatrix_apply,
      Matrix.map_apply, _root_.Polynomial.coe_mapRingHom, _root_.Polynomial.coeff_map,
      sourceLeading_reverseHessian_coeff, if_pos hj]

/-- The actual reverse Hessian in the normalized characteristic frame,
constant in s but not assumed constant in t. -/
def sourceLeading_lineSchurFrame
    {E : Type*} [CommRing E] [Algebra K E]
    (F : StationarySource K) (m : ℕ) (z V : Unit ⊕ Fin 3 → E) :
    GeneralFourBlock (_root_.Polynomial (_root_.Polynomial E)) :=
  transverseCharacteristicFrame (sourceLeading_lineBlock F m z V)
    (_root_.Polynomial.C (_root_.Polynomial.C (V (.inr 0))))
    (_root_.Polynomial.C (_root_.Polynomial.C (V (.inr 1))))
    (_root_.Polynomial.C (_root_.Polynomial.C (V (.inr 2))))

theorem sourceLeading_lineSchurFrame_det
    {E : Type*} [CommRing E] [Algebra K E]
    (F : StationarySource K) (m : ℕ) (hm : 2 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E) :
    (sourceLeading_lineSchurFrame F m z V).determinantCore =
      _root_.Polynomial.monomial (4*m-6) (lineEval z V (MvPolynomial.C δ)) := by
  unfold sourceLeading_lineSchurFrame
  rw [transverseCharacteristicFrame_det, sourceLeading_lineBlock_det F m hm hcap hdet]

theorem sourceLeading_lineSchurFrame_coeff
    {E : Type*} [CommRing E] [Algebra K E]
    (F : StationarySource K) (m j : ℕ) (hj : j ≤ m)
    (z V : Unit ⊕ Fin 3 → E) :
    transverseBlockCoeff (sourceLeading_lineSchurFrame F m z V) j =
      transverseCharacteristicFrame
        (sourceLineBlockOfMatrix ((lineEval z V).toRingHom.mapMatrix
          (hessian (initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F))))
        (_root_.Polynomial.C (V (.inr 0)))
        (_root_.Polynomial.C (V (.inr 1)))
        (_root_.Polynomial.C (V (.inr 2))) := by
  unfold sourceLeading_lineSchurFrame
  rw [transverseCharacteristicFrame_coeff, sourceLeading_lineBlock_coeff F m j hj]

/-- Exact second constraint in the actual line-time coefficient ring.
The kernel-frame hypotheses will be extracted from gradient transport
and the regular transverse anchor, not supplied as source assumptions. -/
theorem sourceLeading_lineSchurFrame_second_constraint
    {E : Type*} [CommRing E] [IsDomain E] [Algebra K E]
    (F : StationarySource K) (m : ℕ) (hm : 3 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E) :
    let H := sourceLeading_lineSchurFrame F m z V
    H.b.coeff 0 = 0 → H.p.coeff 0 = 0 → H.q.coeff 0 = 0 →
    (transverseSchurDet H).coeff 0 ≠ 0 →
    H.a.coeff 2 * (transverseSchurDet H).coeff 0 =
      transverseSchurMixed
        ({ a := H.a.coeff 2, b := H.b.coeff 1, p := H.p.coeff 1,
           q := H.q.coeff 1, d := H.d.coeff 0, r := H.r.coeff 0,
           s := H.s.coeff 0, x := H.x.coeff 0, y := H.y.coeff 0,
           z := H.z.coeff 0 } : GeneralFourBlock (_root_.Polynomial E)) := by
  let H := sourceLeading_lineSchurFrame F m z V
  change H.b.coeff 0 = 0 → H.p.coeff 0 = 0 → H.q.coeff 0 = 0 →
    (transverseSchurDet H).coeff 0 ≠ 0 → _
  intro hb hp hq hregular
  have hd := sourceLeading_lineSchurFrame_det F m (by omega) hcap hdet z V
  have hz (j : ℕ) (hj : j < 4*m-6) : H.determinantCore.coeff j = 0 := by
    change (sourceLeading_lineSchurFrame F m z V).determinantCore.coeff j = 0
    rw [hd, _root_.Polynomial.coeff_monomial, if_neg (Ne.symm (Nat.ne_of_lt hj))]
  obtain ⟨ha0, ha1⟩ := transverseSchur_longitudinal_zero_one
    H hb hp hq hregular (hz 0 (by omega)) (hz 1 (by omega))
  exact transverseSchur_second_constraint H ha0 ha1 hb hp hq (hz 2 (by omega))




/-! ## Differential meaning of the actual characteristic frame -/

private theorem sourceLineFrame_a_eq_sum {R : Type*} [CommRing R]
    (M : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R)
    (W : Unit ⊕ Fin 3 → R) (hW : W (.inl ()) = 1)
    (hsym : ∀ i j, M i j = M j i) :
    (transverseCharacteristicFrame (sourceLineBlockOfMatrix M)
      (W (.inr 0)) (W (.inr 1)) (W (.inr 2))).a =
      ∑ i : Unit ⊕ Fin 3, ∑ j : Unit ⊕ Fin 3, W i * M i j * W j := by
  classical
  have h01 := hsym (.inr 0) (.inl ())
  have h02 := hsym (.inr 1) (.inl ())
  have h03 := hsym (.inr 2) (.inl ())
  have h12 := hsym (.inr 1) (.inr 0)
  have h13 := hsym (.inr 2) (.inr 0)
  have h23 := hsym (.inr 2) (.inr 1)
  simp [transverseCharacteristicFrame, sourceLineBlockOfMatrix,
    GeneralFourBlock.ofSymmetricMatrix, sourceLineIndex, Matrix.submatrix_apply,
    Fintype.sum_sum_type, Fin.sum_univ_three, hW, h01, h02, h03, h12, h13, h23]
  <;> ring

private theorem sourceLineFrame_mixed_eq_sums {R : Type*} [CommRing R]
    (M : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R)
    (W : Unit ⊕ Fin 3 → R) (hW : W (.inl ()) = 1)
    (hsym : ∀ i j, M i j = M j i) :
    let H := transverseCharacteristicFrame (sourceLineBlockOfMatrix M)
      (W (.inr 0)) (W (.inr 1)) (W (.inr 2))
    H.b = (∑ j, W j * M (.inr 0) j) ∧
    H.p = (∑ j, W j * M (.inr 1) j) ∧
    H.q = (∑ j, W j * M (.inr 2) j) := by
  classical
  have h01 := hsym (.inr 0) (.inl ())
  have h02 := hsym (.inr 1) (.inl ())
  have h03 := hsym (.inr 2) (.inl ())
  have h12 := hsym (.inr 1) (.inr 0)
  have h13 := hsym (.inr 2) (.inr 0)
  have h23 := hsym (.inr 2) (.inr 1)
  refine ⟨?_, ?_, ?_⟩ <;>
    simp [transverseCharacteristicFrame, sourceLineBlockOfMatrix,
      GeneralFourBlock.ofSymmetricMatrix, sourceLineIndex, Matrix.submatrix_apply,
      Fintype.sum_sum_type, Fin.sum_univ_three, hW, h01, h02, h03, h12, h13, h23]
    <;> ring

private theorem sourceLineFrame_transverseDet_eq {R : Type*} [CommRing R]
    (M : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R)
    (u v w : R) (hsym : ∀ i j, M i j = M j i) :
    transverseSchurDet (transverseCharacteristicFrame (sourceLineBlockOfMatrix M)
      u v w) = (M.submatrix Sum.inr Sum.inr).det := by
  rw [Matrix.det_fin_three]
  have h12 := hsym (.inr 1) (.inr 0)
  have h13 := hsym (.inr 2) (.inr 0)
  have h23 := hsym (.inr 2) (.inr 1)
  simp [transverseSchurDet, transverseCharacteristicFrame, sourceLineBlockOfMatrix,
    GeneralFourBlock.ofSymmetricMatrix, sourceLineIndex, Matrix.submatrix_apply,
    h12, h13, h23] <;> ring

private theorem transverseSchurDet_coeff_zero {R : Type*} [CommRing R]
    (H : GeneralFourBlock (_root_.Polynomial R)) :
    (transverseSchurDet H).coeff 0 = transverseSchurDet (transverseBlockCoeff H 0) := by
  simp only [transverseSchurDet, transverseBlockCoeff,
    _root_.Polynomial.coeff_add, _root_.Polynomial.coeff_sub,
    _root_.Polynomial.mul_coeff_zero]

/-- The second line derivative is the actual source Hessian quadratic
form along the original affine characteristic. -/
theorem sourceLine_secondDerivative_eq_hessian
    {E : Type*} [CommRing E] [Algebra K E]
    (z V : Unit ⊕ Fin 3 → E) (Q : StationarySource K) :
    (lineEval z V Q).derivative.derivative =
      ∑ i : Unit ⊕ Fin 3, ∑ j : Unit ⊕ Fin 3,
        _root_.Polynomial.C (V i) * lineEval z V (hessian Q i j) *
          _root_.Polynomial.C (V j) := by
  classical
  rw [transverse_lineEval_derivative]
  simp only [_root_.Polynomial.derivative_sum, _root_.Polynomial.derivative_mul,
    _root_.Polynomial.derivative_C, zero_mul, zero_add]
  simp_rw [transverse_lineEval_derivative, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  apply Finset.sum_congr rfl
  intro j _
  change _root_.Polynomial.C (V i) *
    (_root_.Polynomial.C (V j) * lineEval z V (pderiv j (pderiv i Q))) = _
  rw [hessian_apply]
  ring

/-- At every actual layer, the longitudinal coefficient of the framed
Hessian is precisely the second derivative of that layer in time;
the mixed entries are the first time derivatives of its transverse
gradient. This does not differentiate a nonconstant frame. -/
theorem sourceLeading_lineSchurFrame_differential_coeff
    {E : Type*} [CommRing E] [Algebra K E]
    (F : StationarySource K) (m j : ℕ) (hj : j ≤ m)
    (z V : Unit ⊕ Fin 3 → E) (hV : V (.inl ()) = 1) :
    let H := sourceLeading_lineSchurFrame F m z V
    let Q := initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F
    H.a.coeff j = (lineEval z V Q).derivative.derivative ∧
    H.b.coeff j = (lineEval z V (pderiv (.inr 0) Q)).derivative ∧
    H.p.coeff j = (lineEval z V (pderiv (.inr 1) Q)).derivative ∧
    H.q.coeff j = (lineEval z V (pderiv (.inr 2) Q)).derivative := by
  classical
  let H := sourceLeading_lineSchurFrame F m z V
  let Q := initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F
  let M := (lineEval z V).toRingHom.mapMatrix (hessian Q)
  let W : Unit ⊕ Fin 3 → _root_.Polynomial E :=
    fun i => _root_.Polynomial.C (V i)
  have hW : W (.inl ()) = 1 := by simp [W, hV]
  have hsym (i k : Unit ⊕ Fin 3) : M i k = M k i := by
    change lineEval z V (pderiv k (pderiv i Q)) =
      lineEval z V (pderiv i (pderiv k Q))
    rw [HC4.Newton.pderiv_comm_backport k i]
  have hfr : transverseBlockCoeff H j =
      transverseCharacteristicFrame (sourceLineBlockOfMatrix M)
        (W (.inr 0)) (W (.inr 1)) (W (.inr 2)) :=
    sourceLeading_lineSchurFrame_coeff F m j hj z V
  have ha := sourceLineFrame_a_eq_sum M W hW hsym
  obtain ⟨hb, hp, hq⟩ := sourceLineFrame_mixed_eq_sums M W hW hsym
  change (transverseBlockCoeff H j).a = _ ∧
    (transverseBlockCoeff H j).b = _ ∧
    (transverseBlockCoeff H j).p = _ ∧
    (transverseBlockCoeff H j).q = _
  rw [hfr]
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [ha, sourceLine_secondDerivative_eq_hessian]
    rfl
  · rw [hb, transverse_lineEval_derivative]
    rfl
  · rw [hp, transverse_lineEval_derivative]
    rfl
  · rw [hq, transverse_lineEval_derivative]
    rfl

/-- The leading transverse determinant in the framed series is the
actual transverse Hessian determinant transported along the line. -/
theorem sourceLeading_lineSchurFrame_transverseDet_zero
    {E : Type*} [CommRing E] [Algebra K E]
    (F : StationarySource K) (m : ℕ) (z V : Unit ⊕ Fin 3 → E) :
    (transverseSchurDet (sourceLeading_lineSchurFrame F m z V)).coeff 0 =
      lineEval z V ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix
        Sum.inr Sum.inr).det := by
  classical
  let L := initialForm transverseCubicWeight (m : ℤ) F
  let M := (lineEval z V).toRingHom.mapMatrix (hessian L)
  have hsym (i k : Unit ⊕ Fin 3) : M i k = M k i := by
    change lineEval z V (pderiv k (pderiv i L)) =
      lineEval z V (pderiv i (pderiv k L))
    rw [HC4.Newton.pderiv_comm_backport k i]
  rw [transverseSchurDet_coeff_zero,
    sourceLeading_lineSchurFrame_coeff F m 0 (Nat.zero_le m) z V]
  simp only [Nat.cast_zero, sub_zero]
  rw [sourceLineFrame_transverseDet_eq _ _ _ _ hsym]
  change ((lineEval z V).toRingHom.mapMatrix
    ((hessian L).submatrix Sum.inr Sum.inr)).det = _
  rw [← RingHom.map_det]
  rfl

/-- The leading frame conditions follow from the existing gradient
transport and regular reference anchor, at all transverse degrees. -/
theorem sourceLeading_lineSchurFrame_kernel_regular
    {E : Type*} [CommRing E] [IsDomain E] [Algebra K E]
    (F : StationarySource K) (m : ℕ) (z V : Unit ⊕ Fin 3 → E)
    (hV : V (.inl ()) = 1)
    (hz : MvPolynomial.aeval z
      ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval z V (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)) =
      _root_.Polynomial.C
        (MvPolynomial.aeval z (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)))) :
    let H := sourceLeading_lineSchurFrame F m z V
    H.b.coeff 0 = 0 ∧ H.p.coeff 0 = 0 ∧ H.q.coeff 0 = 0 ∧
      (transverseSchurDet H).coeff 0 ≠ 0 := by
  have hd := sourceLeading_lineSchurFrame_differential_coeff F m 0 (Nat.zero_le m) z V hV
  simp only [Nat.cast_zero, sub_zero] at hd
  obtain ⟨_, hb, hp, hq⟩ := hd
  rw [hgrad (.inr 0), _root_.Polynomial.derivative_C] at hb
  rw [hgrad (.inr 1), _root_.Polynomial.derivative_C] at hp
  rw [hgrad (.inr 2), _root_.Polynomial.derivative_C] at hq
  refine ⟨hb, hp, hq, ?_⟩
  rw [sourceLeading_lineSchurFrame_transverseDet_zero]
  intro h
  have hc := congrArg (fun p : _root_.Polynomial E => p.coeff 0) h
  change (lineEval z V ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix
    Sum.inr Sum.inr).det).coeff 0 = (0 : _root_.Polynomial E).coeff 0 at hc
  rw [cubic_lineEval_coeff_zero, _root_.Polynomial.coeff_zero] at hc
  exact hz hc

/-- Source-honest second-order constraint, with all frame hypotheses
discharged. The left side is the second time derivative of the
actual second lower layer, not an independent unknown. -/
theorem sourceLeading_secondCorrection_lineODE
    {E : Type*} [CommRing E] [IsDomain E] [Algebra K E]
    (F : StationarySource K) (m : ℕ) (hm : 3 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (z V : Unit ⊕ Fin 3 → E) (hV : V (.inl ()) = 1)
    (hz : MvPolynomial.aeval z
      ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval z V (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)) =
      _root_.Polynomial.C
        (MvPolynomial.aeval z (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)))) :
    let H := sourceLeading_lineSchurFrame F m z V
    let Q := initialForm transverseCubicWeight ((m : ℤ)-2) F
    (lineEval z V Q).derivative.derivative * (transverseSchurDet H).coeff 0 =
      transverseSchurMixed
        ({ a := 0, b := H.b.coeff 1, p := H.p.coeff 1,
           q := H.q.coeff 1, d := H.d.coeff 0, r := H.r.coeff 0,
           s := H.s.coeff 0, x := H.x.coeff 0, y := H.y.coeff 0,
           z := H.z.coeff 0 } : GeneralFourBlock (_root_.Polynomial E)) := by
  obtain ⟨hb, hp, hq, hr⟩ :=
    sourceLeading_lineSchurFrame_kernel_regular F m z V hV hz hgrad
  have h := sourceLeading_lineSchurFrame_second_constraint F m hm hcap hdet z V hb hp hq hr
  have ha := (sourceLeading_lineSchurFrame_differential_coeff F m 2 (by omega) z V hV).1
  dsimp only at h ha ⊢
  rw [ha] at h
  simpa only [transverseSchurMixed] using h




/-! ## Time degree estimates in the nilpotent chart

These bounds are on actual polynomials in characteristic time. In
particular they do not assert that a nonlinear shear preserves the
Hessian determinant of the original source.
-/

private abbrev LineTime (K : Type*) [Field K] :=
  _root_.Polynomial (MvPolynomial (Fin 3) K)

private def sourceTimeMatrix (N : Matrix (Fin 3) (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) (LineTime K) :=
  (N.map MvPolynomial.C).map _root_.Polynomial.C

private theorem sourceTimeMatrix_mul
    (N M : Matrix (Fin 3) (Fin 3) K) :
    sourceTimeMatrix (N * M) = sourceTimeMatrix N * sourceTimeMatrix M := by
  simp only [sourceTimeMatrix, Matrix.map_mul]

private theorem sourceTimeMatrix_zero :
    sourceTimeMatrix (0 : Matrix (Fin 3) (Fin 3) K) = 0 := by
  ext i j
  simp [sourceTimeMatrix, Matrix.map_apply]

private theorem sourceTimeMatrix_cube
    (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0) :
    sourceTimeMatrix N ^ 3 = 0 := by
  have h : sourceTimeMatrix (N ^ 3) = 0 := by rw [hN, sourceTimeMatrix_zero]
  have he : sourceTimeMatrix (N ^ 3) = sourceTimeMatrix N ^ 3 := by
    rw [pow_succ N 2, pow_succ (sourceTimeMatrix N) 2, sourceTimeMatrix_mul,
      pow_two N, pow_two (sourceTimeMatrix N), sourceTimeMatrix_mul]
  exact he.symm.trans h

private theorem sourceTimeMatrix_square
    (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 2 = 0) :
    sourceTimeMatrix N ^ 2 = 0 := by
  have h : sourceTimeMatrix (N ^ 2) = 0 := by rw [hN, sourceTimeMatrix_zero]
  simpa only [pow_two, sourceTimeMatrix_mul] using h

def sourceTimePencil (N : Matrix (Fin 3) (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) (LineTime K) :=
  1 + (_root_.Polynomial.X : LineTime K) • sourceTimeMatrix N

def sourceTimePencilInv (N : Matrix (Fin 3) (Fin 3) K) :
    Matrix (Fin 3) (Fin 3) (LineTime K) :=
  1 - (_root_.Polynomial.X : LineTime K) • sourceTimeMatrix N +
    (_root_.Polynomial.X : LineTime K)^2 • sourceTimeMatrix (N^2)

theorem sourceTimePencil_right_inverse
    (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0) :
    sourceTimePencil N * sourceTimePencilInv N = 1 := by
  let A := (_root_.Polynomial.X : LineTime K) • sourceTimeMatrix N
  have h3 : A ^ 3 = 0 := by
    dsimp only [A]
    rw [smul_pow, sourceTimeMatrix_cube N hN, smul_zero]
  have h2 : A ^ 2 =
      (_root_.Polynomial.X : LineTime K)^2 • sourceTimeMatrix (N^2) := by
    dsimp only [A]
    rw [smul_pow, pow_two N, sourceTimeMatrix_mul, pow_two (sourceTimeMatrix N)]
  unfold sourceTimePencil sourceTimePencilInv
  change (1 + A) * (1 - A +
    (_root_.Polynomial.X : LineTime K)^2 • sourceTimeMatrix (N^2)) = 1
  rw [← h2]
  calc
    _ = 1 + A ^ 3 := by
      simp only [add_mul, one_mul, mul_add, mul_sub, mul_one,
        pow_succ' A 2, pow_two A]
      abel
    _ = 1 := by rw [h3, add_zero]

/-- Transverse differentiation in the reference variables: the
actual source gradient times the affine pencil is the gradient of
the pulled-back polynomial. No gradient constancy is needed here. -/
theorem sourceLinear_referenceGradient_chain
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (Q : StationarySource K) :
    (fun i : Fin 3 => linearLineEval a N (pderiv (.inr i) Q)) ᵥ*
      sourceTimePencil N =
      fun j : Fin 3 => coeffDeriv (pderiv j) (linearLineEval a N Q) := by
  classical
  let B := MvPolynomial (Fin 3) K
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let v : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
  let w : Unit ⊕ Fin 3 → _root_.Polynomial B := fun i =>
    _root_.Polynomial.C (z i) + _root_.Polynomial.C (v i) * _root_.Polynomial.X
  have hE : linearLineEval a N = MvPolynomial.aeval w := rfl
  have hz (j k : Fin 3) : pderiv j (z (.inr k)) = if k = j then 1 else 0 := by
    by_cases h : k = j
    · subst k; simp [z]
    · simp [z, h, pderiv_X_of_ne h]
  have hv (j k : Fin 3) : pderiv j (v (.inr k)) = MvPolynomial.C (N k j) := by
    simp only [v, Sum.elim_inr, referenceLinearVector, map_sum, MvPolynomial.pderiv_C_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      rw [pderiv_X_of_ne hi, mul_zero]
    · simp
  have hC (j : Fin 3) (b : B) :
      coeffDeriv (pderiv j : Derivation K B B) (_root_.Polynomial.C b) =
        _root_.Polynomial.C (pderiv j b) :=
    coeffDeriv_C (pderiv j : Derivation K B B) b
  have hc (j : Fin 3) : coeffDeriv (pderiv j : Derivation K B B) (w (.inl ())) = 0 := by
    simp [w, z, v]
    calc
      _ = _root_.Polynomial.C (pderiv j (MvPolynomial.C a : B)) :=
        hC j (MvPolynomial.C a)
      _ = 0 := by simp
  have ht (j k : Fin 3) :
      coeffDeriv (pderiv j : Derivation K B B) (w (.inr k)) =
        sourceTimePencil N k j := by
    change coeffDeriv (pderiv j : Derivation K B B)
      (_root_.Polynomial.C (z (.inr k)) +
      _root_.Polynomial.C (v (.inr k)) * _root_.Polynomial.X) = _
    simp only [map_add, Derivation.leibniz, smul_eq_mul, coeffDeriv_X,
      mul_zero, zero_add, sourceTimePencil, sourceTimeMatrix,
      Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.map_apply]
    calc
      _ = _root_.Polynomial.C (pderiv j (z (.inr k))) +
          _root_.Polynomial.X * _root_.Polynomial.C (pderiv j (v (.inr k))) :=
        congrArg₂ (fun x y : _root_.Polynomial B => x + _root_.Polynomial.X * y)
          (hC j (z (.inr k))) (hC j (v (.inr k)))
      _ = _ := by
        rw [hz j k, hv j k]
        split_ifs <;> simp <;> exact mul_comm _ _
  funext j
  change (∑ i : Fin 3, linearLineEval a N (pderiv (.inr i) Q) *
    sourceTimePencil N i j) = coeffDeriv (pderiv j) (linearLineEval a N Q)
  rw [hE, derivation_aeval]
  simp only [Fintype.sum_sum_type, hc, mul_zero, Finset.sum_const_zero, zero_add, ht]

theorem sourceTime_coeffDeriv_natDegree_le
    (D : Derivation K (MvPolynomial (Fin 3) K) (MvPolynomial (Fin 3) K))
    (P : LineTime K) :
    (coeffDeriv D P).natDegree ≤ P.natDegree := by
  apply _root_.Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [coeff_coeffDeriv, _root_.Polynomial.coeff_eq_zero_of_natDegree_lt hk, map_zero]

theorem sourceTime_natDegree_sum_le
    {R I : Type*} [CommRing R] (s : Finset I) (f : I → _root_.Polynomial R)
    (d : ℕ) (h : ∀ i ∈ s, (f i).natDegree ≤ d) :
    (∑ i ∈ s, f i).natDegree ≤ d := by
  apply _root_.Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  rw [_root_.Polynomial.finset_sum_coeff]
  apply Finset.sum_eq_zero
  intro i hi
  exact _root_.Polynomial.coeff_eq_zero_of_natDegree_lt ((h i hi).trans_lt hk)

private theorem sourceTimePencilInv_natDegree_le
    (N : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (sourceTimePencilInv N i j).natDegree ≤ 2 := by
  have h1 : (1 : Matrix (Fin 3) (Fin 3) (LineTime K)) i j =
      if i = j then 1 else 0 := by rw [Matrix.one_apply]
  have hd : ((1 : Matrix (Fin 3) (Fin 3) (LineTime K)) i j).natDegree ≤ 0 := by
    rw [h1]
    split_ifs <;> simp
  have hlin : ((_root_.Polynomial.X : LineTime K) *
      sourceTimeMatrix N i j).natDegree ≤ 1 := by
    change (_root_.Polynomial.X * _root_.Polynomial.C (MvPolynomial.C (N i j))).natDegree ≤ 1
    exact (_root_.Polynomial.natDegree_mul_C_le _ _).trans (by simp)
  have hquad : (((_root_.Polynomial.X : LineTime K)^2) *
      sourceTimeMatrix (N^2) i j).natDegree ≤ 2 := by
    change (_root_.Polynomial.X ^ 2 *
      _root_.Polynomial.C (MvPolynomial.C ((N^2) i j))).natDegree ≤ 2
    exact (_root_.Polynomial.natDegree_mul_C_le _ _).trans (by simp)
  simp only [sourceTimePencilInv, Matrix.add_apply, Matrix.sub_apply,
    Matrix.smul_apply, smul_eq_mul]
  exact _root_.Polynomial.natDegree_add_le_of_degree_le
    ((_root_.Polynomial.natDegree_sub_le _ _).trans (max_le (hd.trans (by omega))
      (hlin.trans (by omega)))) hquad

/-- Each actual transverse partial derivative costs at most two
characteristic-time degrees, uniformly in the transverse layer.
This is the cube-zero estimate needed for the degree induction. -/
theorem sourceNilpotent_transverseGradient_timeDegree_le
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (Q : StationarySource K) (i : Fin 3) :
    (linearLineEval a N (pderiv (.inr i) Q)).natDegree ≤
      (linearLineEval a N Q).natDegree + 2 := by
  classical
  let G : Fin 3 → LineTime K := fun j => linearLineEval a N (pderiv (.inr j) Q)
  let D : Fin 3 → LineTime K := fun j => coeffDeriv (pderiv j) (linearLineEval a N Q)
  have h : G ᵥ* sourceTimePencil N = D := sourceLinear_referenceGradient_chain a N Q
  have he : G = D ᵥ* sourceTimePencilInv N := by
    calc
      G = G ᵥ* (1 : Matrix (Fin 3) (Fin 3) (LineTime K)) :=
        (Matrix.vecMul_one G).symm
      _ = G ᵥ* (sourceTimePencil N * sourceTimePencilInv N) := by
        rw [sourceTimePencil_right_inverse N hN]
      _ = (G ᵥ* sourceTimePencil N) ᵥ* sourceTimePencilInv N :=
        (Matrix.vecMul_vecMul G _ _).symm
      _ = _ := by rw [h]
  change (G i).natDegree ≤ _
  rw [he]
  change (∑ j : Fin 3, D j * sourceTimePencilInv N j i).natDegree ≤ _
  apply sourceTime_natDegree_sum_le
  intro j _
  exact _root_.Polynomial.natDegree_mul_le_of_le
    (sourceTime_coeffDeriv_natDegree_le (pderiv j) (linearLineEval a N Q))
    (sourceTimePencilInv_natDegree_le N j i)

/-- Two actual transverse derivatives cost at most four time degrees.
The estimate applies to every lower source layer. -/
theorem sourceNilpotent_transverseHessian_timeDegree_le
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (Q : StationarySource K) (i j : Fin 3) :
    (linearLineEval a N (hessian Q (.inr i) (.inr j))).natDegree ≤
      (linearLineEval a N Q).natDegree + 4 := by
  change (linearLineEval a N (pderiv (.inr j) (pderiv (.inr i) Q))).natDegree ≤ _
  have h1 := sourceNilpotent_transverseGradient_timeDegree_le a N hN Q i
  have h2 := sourceNilpotent_transverseGradient_timeDegree_le a N hN (pderiv (.inr i) Q) j
  omega

/-- A first mixed characteristic derivative costs at most one time
degree in the cube-zero chart (including the constant case). -/
theorem sourceNilpotent_mixed_timeDegree_le
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (Q : StationarySource K) (i : Fin 3) :
    (linearLineEval a N (pderiv (.inr i) Q)).derivative.natDegree ≤
      (linearLineEval a N Q).natDegree + 1 := by
  have h1 := sourceNilpotent_transverseGradient_timeDegree_le a N hN Q i
  have h2 := _root_.Polynomial.natDegree_derivative_le
    (linearLineEval a N (pderiv (.inr i) Q))
  omega




/-! ## Leading transverse adjugate and a quantitative second correction -/

theorem sourceTimePencil_natDegree_le
    (N : Matrix (Fin 3) (Fin 3) K) (i j : Fin 3) :
    (sourceTimePencil N i j).natDegree ≤ 1 := by
  have hd : ((1 : Matrix (Fin 3) (Fin 3) (LineTime K)) i j).natDegree ≤ 0 := by
    rw [Matrix.one_apply]
    split_ifs <;> simp
  have hlin : ((_root_.Polynomial.X : LineTime K) *
      sourceTimeMatrix N i j).natDegree ≤ 1 := by
    change (_root_.Polynomial.X * _root_.Polynomial.C (MvPolynomial.C (N i j))).natDegree ≤ 1
    exact (_root_.Polynomial.natDegree_mul_C_le _ _).trans (by simp)
  simp only [sourceTimePencil, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]
  exact _root_.Polynomial.natDegree_add_le_of_degree_le (hd.trans (by omega)) hlin

/-- The leading transverse adjugate is affine in characteristic time,
even when the leading transverse Hessian itself is quadratic in time.
The determinant is the original nonzero reference determinant. -/
theorem sourceLinear_leadingAdjugate_transport
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (L : StationarySource K)
    (hreg : referenceSlice a ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Fin 3, linearLineEval a N (pderiv (.inr i) L) =
      _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L))) :
    let H := (hessian L).submatrix Sum.inr Sum.inr
    let T := (linearLineEval a N).toRingHom.mapMatrix H
    let M := (referenceSlice a).toRingHom.mapMatrix H
    T.det = _root_.Polynomial.C (referenceSlice a H.det) ∧
      T.adjugate = sourceTimePencil N * M.adjugate.map _root_.Polynomial.C := by
  classical
  let B := MvPolynomial (Fin 3) K
  let H := (hessian L).submatrix Sum.inr Sum.inr
  let T := (linearLineEval a N).toRingHom.mapMatrix H
  let M := (referenceSlice a).toRingHom.mapMatrix H
  let J := sourceTimePencil N
  have h : T * J = M.map _root_.Polynomial.C :=
    transverseHessian_transport_of_linear_gradient a N L hgrad
  let J0 : Matrix (Fin 3) (Fin 3) (_root_.Polynomial K) :=
    1 + (_root_.Polynomial.X : _root_.Polynomial K) • N.map _root_.Polynomial.C
  have hJ0 : J0.det = 1 := det_linearCharacteristic_eq_one a N L hreg hgrad
  let f := _root_.Polynomial.mapRingHom (MvPolynomial.C : K →+* B)
  have hmap : f.mapMatrix J0 = J := by
    ext i j
    by_cases hij : i = j <;>
      simp [f, J0, J, sourceTimePencil, sourceTimeMatrix, hij, Matrix.smul_apply,
        smul_eq_mul, RingHom.mapMatrix_apply, _root_.Polynomial.map_add, _root_.Polynomial.map_mul]
  have hJ : J.det = 1 := by
    rw [← hmap, ← RingHom.map_det, hJ0, map_one]
  have hdet : T.det = _root_.Polynomial.C (referenceSlice a H.det) := by
    have hh := congrArg Matrix.det h
    change (T * J).det = (M.map _root_.Polynomial.C).det at hh
    rw [Matrix.det_mul, hJ, mul_one] at hh
    calc
      _ = (M.map _root_.Polynomial.C).det := hh
      _ = _ := (_root_.Polynomial.C.map_det M).symm.trans
        (congrArg _root_.Polynomial.C ((referenceSlice a).map_det H).symm)
  have hadj : (M.map _root_.Polynomial.C).adjugate = J.adjugate * T.adjugate := by
    rw [← h, Matrix.adjugate_mul_distrib]
  have hC : (M.map _root_.Polynomial.C).adjugate =
      M.adjugate.map _root_.Polynomial.C :=
    (_root_.Polynomial.C.map_adjugate M).symm
  refine ⟨hdet, ?_⟩
  calc
    T.adjugate = (J * J.adjugate) * T.adjugate := by
      rw [Matrix.mul_adjugate, hJ, one_smul, one_mul]
    _ = J * (J.adjugate * T.adjugate) := mul_assoc _ _ _
    _ = J * M.adjugate.map _root_.Polynomial.C := by rw [← hadj, hC]

theorem sourceLinear_leadingAdjugate_timeDegree_le
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (L : StationarySource K)
    (hreg : referenceSlice a ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Fin 3, linearLineEval a N (pderiv (.inr i) L) =
      _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L)))
    (i j : Fin 3) :
    (((linearLineEval a N).toRingHom.mapMatrix
      ((hessian L).submatrix Sum.inr Sum.inr)).adjugate i j).natDegree ≤ 1 := by
  classical
  rw [(sourceLinear_leadingAdjugate_transport a N L hreg hgrad).2]
  rw [Matrix.mul_apply]
  apply sourceTime_natDegree_sum_le
  intro k _
  change (sourceTimePencil N i k *
    _root_.Polynomial.C (((referenceSlice a).toRingHom.mapMatrix
      ((hessian L).submatrix Sum.inr Sum.inr)).adjugate k j)).natDegree ≤ 1
  exact (_root_.Polynomial.natDegree_mul_C_le _ _).trans
    (sourceTimePencil_natDegree_le N i k)

/-- Express the scalar mixed Schur correction as the quadratic pairing
with the adjugate of the actual transverse matrix. -/
theorem sourceLineFrame_mixed_adjugate {R : Type*} [CommRing R]
    (H : GeneralFourBlock R) (T : Matrix (Fin 3) (Fin 3) R)
    (hd : H.d = T 0 0) (hr : H.r = T 0 1) (hs : H.s = T 0 2)
    (hx : H.x = T 1 1) (hy : H.y = T 1 2) (hz : H.z = T 2 2)
    (hSym : ∀ i j, T i j = T j i) :
    transverseSchurMixed H =
      ∑ i : Fin 3, ∑ j : Fin 3,
        (![H.b, H.p, H.q] : Fin 3 → R) i * T.adjugate i j *
          (![H.b, H.p, H.q] : Fin 3 → R) j := by
  classical
  have h10 := hSym 1 0
  have h20 := hSym 2 0
  have h21 := hSym 2 1
  rw [Matrix.adjugate_fin_three]
  simp [transverseSchurMixed, hd, hr, hs, hx, hy, hz,
    Fin.sum_univ_three, h10, h20, h21] <;> ring

private theorem sourceTime_degree_of_secondDerivative_le
    {R : Type*} [CommRing R] [IsDomain R] [CharZero R]
    (P : _root_.Polynomial R) (d : ℕ)
    (h : P.derivative.derivative.natDegree ≤ d) :
    P.natDegree ≤ d + 2 := by
  apply _root_.Polynomial.natDegree_le_iff_coeff_eq_zero.mpr
  intro k hk
  have hc : P.derivative.derivative.coeff (k-2) = 0 :=
    _root_.Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)
  rw [_root_.Polynomial.coeff_derivative, _root_.Polynomial.coeff_derivative] at hc
  have he : k - 2 + 1 + 1 = k := by omega
  rw [he] at hc
  have h1 : ((k - 2 + 1 : ℕ) : R) ≠ 0 := by exact_mod_cast (by omega : k - 2 + 1 ≠ 0)
  have h2 : (k : R) ≠ 0 := by exact_mod_cast (by omega : k ≠ 0)
  have hc' : (P.coeff k * (k : R)) * ((k - 2 + 1 : ℕ) : R) = 0 := by
    have heR : ((k - 2 : ℕ) : R) + 1 + 1 = (k : R) := by
      exact_mod_cast he
    simpa only [Nat.cast_add, Nat.cast_one, heR] using hc
  exact (mul_eq_zero.mp ((mul_eq_zero.mp hc').resolve_right h1)).resolve_right h2

/-- Actual second lower layer degree bound, not merely a bound on
abstract Schur variables. The constant leading determinant cancels
without any localization. -/
theorem sourceNilpotent_secondCorrection_timeDegree_le_seven
    (F : StationarySource K) (m : ℕ) (hm : 3 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (hreg : referenceSlice a
      ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)) =
        _root_.Polynomial.C (referenceSlice a
          (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)))) :
    (linearLineEval a N (initialForm transverseCubicWeight ((m : ℤ)-2) F)).natDegree ≤ 7 := by
  classical
  let B := MvPolynomial (Fin 3) K
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
  let L := initialForm transverseCubicWeight (m : ℤ) F
  let Q := initialForm transverseCubicWeight ((m : ℤ)-1) F
  let P := linearLineEval a N (initialForm transverseCubicWeight ((m : ℤ)-2) F)
  let H := sourceLeading_lineSchurFrame F m z V
  let T := (linearLineEval a N).toRingHom.mapMatrix ((hessian L).submatrix Sum.inr Sum.inr)
  have hV : V (.inl ()) = 1 := rfl
  have hz : MvPolynomial.aeval z ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0 := hreg
  have hg : ∀ i, lineEval z V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval z (pderiv i L)) := hgrad
  have haff := sourceNilpotent_firstCorrection_affine F (m : ℤ) (by omega)
    hcap hdet a N hreg hgrad
  have hQ : (linearLineEval a N Q).natDegree ≤ 1 := by
    change (linearLineEval a N Q).natDegree ≤ 1
    have he : linearLineEval a N Q =
        _root_.Polynomial.C ((linearLineEval a N Q).coeff 0) +
        _root_.Polynomial.C ((linearLineEval a N Q).coeff 1) * _root_.Polynomial.X := haff
    calc
      _ = (_root_.Polynomial.C ((linearLineEval a N Q).coeff 0) +
        _root_.Polynomial.C ((linearLineEval a N Q).coeff 1) * _root_.Polynomial.X).natDegree :=
        congrArg _root_.Polynomial.natDegree he
      _ ≤ 1 := _root_.Polynomial.natDegree_add_le_of_degree_le (by simp)
        ((_root_.Polynomial.natDegree_C_mul_le _ _).trans (by simp))
  have hc := sourceLeading_lineSchurFrame_differential_coeff F m 1 (by omega) z V hV
  obtain ⟨_, hb, hp, hq⟩ := hc
  let W : Fin 3 → LineTime K := ![H.b.coeff 1, H.p.coeff 1, H.q.coeff 1]
  have hW (i : Fin 3) : (W i).natDegree ≤ 2 := by
    fin_cases i
    · change (H.b.coeff 1).natDegree ≤ 2
      change H.b.coeff 1 = (linearLineEval a N (pderiv (.inr 0) Q)).derivative at hb
      rw [hb]
      exact (sourceNilpotent_mixed_timeDegree_le a N hN Q 0).trans (by omega)
    · change (H.p.coeff 1).natDegree ≤ 2
      change H.p.coeff 1 = (linearLineEval a N (pderiv (.inr 1) Q)).derivative at hp
      rw [hp]
      exact (sourceNilpotent_mixed_timeDegree_le a N hN Q 1).trans (by omega)
    · change (H.q.coeff 1).natDegree ≤ 2
      change H.q.coeff 1 = (linearLineEval a N (pderiv (.inr 2) Q)).derivative at hq
      rw [hq]
      exact (sourceNilpotent_mixed_timeDegree_le a N hN Q 2).trans (by omega)
  have ht : ∀ i : Fin 3, linearLineEval a N (pderiv (.inr i) L) =
      _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L)) := fun i => hgrad (.inr i)
  have hAdj (i j : Fin 3) : (T.adjugate i j).natDegree ≤ 1 :=
    sourceLinear_leadingAdjugate_timeDegree_le a N L hreg ht i j
  have hsum : (∑ i : Fin 3, ∑ j : Fin 3, W i * T.adjugate i j * W j).natDegree ≤ 5 := by
    apply sourceTime_natDegree_sum_le
    intro i _
    apply sourceTime_natDegree_sum_le
    intro j _
    exact _root_.Polynomial.natDegree_mul_le_of_le
      (_root_.Polynomial.natDegree_mul_le_of_le (hW i) (hAdj i j)) (hW j)
  have hsym (i j : Fin 3) : T i j = T j i := by
    change linearLineEval a N (pderiv (.inr j) (pderiv (.inr i) L)) =
      linearLineEval a N (pderiv (.inr i) (pderiv (.inr j) L))
    rw [HC4.Newton.pderiv_comm_backport]
  let U : GeneralFourBlock (LineTime K) :=
    { a := 0, b := H.b.coeff 1, p := H.p.coeff 1, q := H.q.coeff 1,
      d := H.d.coeff 0, r := H.r.coeff 0, s := H.s.coeff 0,
      x := H.x.coeff 0, y := H.y.coeff 0, z := H.z.coeff 0 }
  have he := sourceLeading_lineSchurFrame_coeff F m 0 (Nat.zero_le m) z V
  simp only [Nat.cast_zero, sub_zero] at he
  have hu : transverseSchurMixed U = ∑ i : Fin 3, ∑ j : Fin 3,
      W i * T.adjugate i j * W j := by
    apply sourceLineFrame_mixed_adjugate U T <;> try exact hsym
    · exact congrArg GeneralFourBlock.d he
    · exact congrArg GeneralFourBlock.r he
    · exact congrArg GeneralFourBlock.s he
    · exact congrArg GeneralFourBlock.x he
    · exact congrArg GeneralFourBlock.y he
    · exact congrArg GeneralFourBlock.z he
  have hODE := sourceLeading_secondCorrection_lineODE F m hm hcap hdet z V hV hz hg
  change P.derivative.derivative * (transverseSchurDet H).coeff 0 =
    transverseSchurMixed U at hODE
  have hd : (transverseSchurDet H).coeff 0 =
      _root_.Polynomial.C (referenceSlice a ((hessian L).submatrix Sum.inr Sum.inr).det) := by
    change (transverseSchurDet (sourceLeading_lineSchurFrame F m z V)).coeff 0 = _
    rw [sourceLeading_lineSchurFrame_transverseDet_zero]
    change (linearLineEval a N).toRingHom ((hessian L).submatrix Sum.inr Sum.inr).det = _
    rw [RingHom.map_det]
    exact (sourceLinear_leadingAdjugate_transport a N L hreg ht).1
  rw [hd, hu] at hODE
  have hdeg := congrArg _root_.Polynomial.natDegree hODE
  change (P.derivative.derivative * _root_.Polynomial.C
    (referenceSlice a ((hessian L).submatrix Sum.inr Sum.inr).det)).natDegree = _ at hdeg
  rw [_root_.Polynomial.natDegree_mul_C hreg] at hdeg
  exact sourceTime_degree_of_secondDerivative_le P 5 (hdeg.trans_le hsum)




/-! ## Uniform cleared Schur degree induction

The degree profile distinguishes the zero Rees coefficient of the
transverse block from positive coefficients. Both mixed factors have
zero constant coefficient. These are essential, not optional, savings
in the convolution estimate.
-/

section TimeDegreeInduction

variable {R : Type*} [CommRing R]
local notation "TP" => _root_.Polynomial R
local notation "RP" => _root_.Polynomial TP

private theorem sourceTime_mul_coeff_degree_le
    (p q : RP) (n d : ℕ)
    (h : ∀ i j : ℕ, i+j=n → (p.coeff i * q.coeff j).natDegree ≤ d) :
    ((p*q).coeff n).natDegree ≤ d := by
  rw [_root_.Polynomial.coeff_mul]
  apply sourceTime_natDegree_sum_le
  intro ij hij
  exact h ij.1 ij.2 (Finset.mem_antidiagonal.mp hij)

private theorem sourceTime_add_coeff_degree_le
    {p q : RP} {n d : ℕ}
    (hp : (p.coeff n).natDegree ≤ d) (hq : (q.coeff n).natDegree ≤ d) :
    ((p+q).coeff n).natDegree ≤ d := by
  rw [_root_.Polynomial.coeff_add]
  exact _root_.Polynomial.natDegree_add_le_of_degree_le hp hq

private theorem sourceTime_sub_coeff_degree_le
    {p q : RP} {n d : ℕ}
    (hp : (p.coeff n).natDegree ≤ d) (hq : (q.coeff n).natDegree ≤ d) :
    ((p-q).coeff n).natDegree ≤ d := by
  rw [_root_.Polynomial.coeff_sub]
  exact (_root_.Polynomial.natDegree_sub_le _ _).trans (max_le hp hq)

def timeTransverseProfile (k : ℕ) : ℕ :=
  if k = 0 then 2 else 9*k-4

private def timeMinorProfile (k : ℕ) : ℕ :=
  if k = 0 then 4 else 9*k-2

private def timeDetProfile (k : ℕ) : ℕ :=
  if k = 0 then 6 else 9*k

private theorem sourceTime_transverse_pair
    (p q : RP) (n k : ℕ) (hk : k < n)
    (hp : ∀ i < n, (p.coeff i).natDegree ≤ timeTransverseProfile i)
    (hq : ∀ i < n, (q.coeff i).natDegree ≤ timeTransverseProfile i) :
    ((p*q).coeff k).natDegree ≤ timeMinorProfile k := by
  apply sourceTime_mul_coeff_degree_le
  intro i j hij
  have hi := hp i (by omega)
  have hj := hq j (by omega)
  have hdeg := _root_.Polynomial.natDegree_mul_le_of_le hi hj
  simp only [timeTransverseProfile, timeMinorProfile] at hdeg ⊢
  split_ifs at hdeg ⊢ <;> omega

private theorem sourceTime_transverse_triple
    (p q : RP) (n k : ℕ) (hk : k < n)
    (hp : ∀ i < n, (p.coeff i).natDegree ≤ timeTransverseProfile i)
    (hq : ∀ i < n, (q.coeff i).natDegree ≤ timeMinorProfile i) :
    ((p*q).coeff k).natDegree ≤ timeDetProfile k := by
  apply sourceTime_mul_coeff_degree_le
  intro i j hij
  have hi := hp i (by omega)
  have hj := hq j (by omega)
  have hdeg := _root_.Polynomial.natDegree_mul_le_of_le hi hj
  simp only [timeTransverseProfile, timeMinorProfile, timeDetProfile] at hdeg ⊢
  split_ifs at hdeg ⊢ <;> omega

private theorem sourceTime_mixed_pair_zero
    (p q : RP) (hp : p.coeff 0 = 0) (hq : q.coeff 0 = 0)
    (k : ℕ) (hk : k < 2) : (p*q).coeff k = 0 := by
  rw [_root_.Polynomial.coeff_mul]
  apply Finset.sum_eq_zero
  intro ij hij
  have hh := Finset.mem_antidiagonal.mp hij
  by_cases hi : ij.1 = 0
  · rw [hi, hp, zero_mul]
  · have hj : ij.2 = 0 := by omega
    rw [hj, hq, mul_zero]

private theorem sourceTime_mixed_pair
    (p q : RP) (n k : ℕ) (hk : k ≤ n)
    (hp0 : p.coeff 0 = 0) (hq0 : q.coeff 0 = 0)
    (hp : ∀ i < n, 0 < i → (p.coeff i).natDegree ≤ 9*i-7)
    (hq : ∀ i < n, 0 < i → (q.coeff i).natDegree ≤ 9*i-7) :
    ((p*q).coeff k).natDegree ≤ 9*k-14 := by
  apply sourceTime_mul_coeff_degree_le
  intro i j hij
  by_cases hi : i = 0
  · rw [hi, hp0, zero_mul, _root_.Polynomial.natDegree_zero]
    exact Nat.zero_le _
  by_cases hj : j = 0
  · rw [hj, hq0, mul_zero, _root_.Polynomial.natDegree_zero]
    exact Nat.zero_le _
  have hdeg := _root_.Polynomial.natDegree_mul_le_of_le
    (hp i (by omega) (by omega)) (hq j (by omega) (by omega))
  omega

private theorem sourceTime_mixed_minor
    (p q r : RP) (n : ℕ) (hn : 2 ≤ n)
    (hp0 : p.coeff 0 = 0) (hq0 : q.coeff 0 = 0)
    (hp : ∀ i < n, 0 < i → (p.coeff i).natDegree ≤ 9*i-7)
    (hq : ∀ i < n, 0 < i → (q.coeff i).natDegree ≤ 9*i-7)
    (hr : ∀ i < n, (r.coeff i).natDegree ≤ timeMinorProfile i) :
    ((p*q*r).coeff n).natDegree ≤ 9*n-10 := by
  apply sourceTime_mul_coeff_degree_le
  intro i j hij
  by_cases hi : i < 2
  · rw [sourceTime_mixed_pair_zero p q hp0 hq0 i hi, zero_mul,
      _root_.Polynomial.natDegree_zero]
    exact Nat.zero_le _
  have hpq := sourceTime_mixed_pair p q n i (by omega) hp0 hq0 hp hq
  have hminor := hr j (by omega)
  have hdeg := _root_.Polynomial.natDegree_mul_le_of_le hpq hminor
  unfold timeMinorProfile at hdeg
  split_ifs at hdeg <;> omega

/-- Pure coefficient induction step. No formal inverse and no
hypothesis on higher coefficients is used. -/
theorem transverseSchur_cleared_timeDegree_step [IsDomain R]
    (H : GeneralFourBlock RP) (n : ℕ) (hn : 2 ≤ n)
    (c : R) (hc : c ≠ 0)
    (hconstant : (transverseSchurDet H).coeff 0 = _root_.Polynomial.C c)
    (hclock : H.determinantCore.coeff n = 0)
    (ha0 : H.a.coeff 0 = 0) (ha1 : H.a.coeff 1 = 0)
    (hb0 : H.b.coeff 0 = 0) (hp0 : H.p.coeff 0 = 0) (hq0 : H.q.coeff 0 = 0)
    (ha : ∀ i < n, 2 ≤ i → (H.a.coeff i).natDegree ≤ 9*i-10)
    (hb : ∀ i < n, 0 < i → (H.b.coeff i).natDegree ≤ 9*i-7)
    (hp : ∀ i < n, 0 < i → (H.p.coeff i).natDegree ≤ 9*i-7)
    (hq : ∀ i < n, 0 < i → (H.q.coeff i).natDegree ≤ 9*i-7)
    (hd : ∀ i < n, (H.d.coeff i).natDegree ≤ timeTransverseProfile i)
    (hr : ∀ i < n, (H.r.coeff i).natDegree ≤ timeTransverseProfile i)
    (hs : ∀ i < n, (H.s.coeff i).natDegree ≤ timeTransverseProfile i)
    (hx : ∀ i < n, (H.x.coeff i).natDegree ≤ timeTransverseProfile i)
    (hy : ∀ i < n, (H.y.coeff i).natDegree ≤ timeTransverseProfile i)
    (hz : ∀ i < n, (H.z.coeff i).natDegree ≤ timeTransverseProfile i) :
    (H.a.coeff n).natDegree ≤ 9*n-10 := by
  classical
  have minor {p q r s : RP}
      (hp : ∀ i < n, (p.coeff i).natDegree ≤ timeTransverseProfile i)
      (hq : ∀ i < n, (q.coeff i).natDegree ≤ timeTransverseProfile i)
      (hr : ∀ i < n, (r.coeff i).natDegree ≤ timeTransverseProfile i)
      (hs : ∀ i < n, (s.coeff i).natDegree ≤ timeTransverseProfile i)
      (k : ℕ) (hk : k < n) :
      ((p*q-r*s).coeff k).natDegree ≤ timeMinorProfile k :=
    sourceTime_sub_coeff_degree_le
      (sourceTime_transverse_pair p q n k hk hp hq)
      (sourceTime_transverse_pair r s n k hk hr hs)
  have m1 := minor hx hz hy hy
  have m2 := minor hr hz hs hy
  have m3 := minor hr hy hs hx
  have m4 := minor hd hz hs hs
  have m5 := minor hd hy hr hs
  have m6 := minor hd hx hr hr
  have hD (k : ℕ) (hk : k < n) :
      ((transverseSchurDet H).coeff k).natDegree ≤ timeDetProfile k := by
    unfold transverseSchurDet
    exact sourceTime_add_coeff_degree_le
      (sourceTime_sub_coeff_degree_le
        (sourceTime_transverse_triple _ _ n k hk hd m1)
        (sourceTime_transverse_triple _ _ n k hk hr m2))
      (sourceTime_transverse_triple _ _ n k hk hs m3)
  have hM : ((transverseSchurMixed H).coeff n).natDegree ≤ 9*n-10 := by
    unfold transverseSchurMixed
    exact sourceTime_add_coeff_degree_le
      (sourceTime_sub_coeff_degree_le
        (sourceTime_add_coeff_degree_le
          (sourceTime_add_coeff_degree_le
            (sourceTime_sub_coeff_degree_le
              (sourceTime_mixed_minor _ _ _ n hn hb0 hb0 hb hb m1)
              (sourceTime_mixed_minor _ _ _ n hn hb0 hp0 hb hp
                (fun k hk => sourceTime_add_coeff_degree_le (m2 k hk) (m2 k hk))))
            (sourceTime_mixed_minor _ _ _ n hn hb0 hq0 hb hq
              (fun k hk => sourceTime_add_coeff_degree_le (m3 k hk) (m3 k hk))))
          (sourceTime_mixed_minor _ _ _ n hn hp0 hp0 hp hp m4))
        (sourceTime_mixed_minor _ _ _ n hn hp0 hq0 hp hq
          (fun k hk => sourceTime_add_coeff_degree_le (m5 k hk) (m5 k hk))))
      (sourceTime_mixed_minor _ _ _ n hn hq0 hq0 hq hq m6)
  have hsum : (∑ ij ∈ (Finset.antidiagonal n).erase (n, 0),
      H.a.coeff ij.1 * (transverseSchurDet H).coeff ij.2).natDegree ≤ 9*n-10 := by
    apply sourceTime_natDegree_sum_le
    intro ij hij
    have hh := Finset.mem_antidiagonal.mp (Finset.mem_of_mem_erase hij)
    have hne := Finset.ne_of_mem_erase hij
    have hj : 0 < ij.2 := by
      by_contra! h
      apply hne
      exact Prod.ext (by omega) (by omega)
    by_cases hi0 : ij.1 = 0
    · rw [hi0, ha0, zero_mul, _root_.Polynomial.natDegree_zero]
      exact Nat.zero_le _
    by_cases hi1 : ij.1 = 1
    · rw [hi1, ha1, zero_mul, _root_.Polynomial.natDegree_zero]
      exact Nat.zero_le _
    have h1 := ha ij.1 (by omega) (by omega)
    have h2 := hD ij.2 (by omega)
    have hdeg := _root_.Polynomial.natDegree_mul_le_of_le h1 h2
    unfold timeDetProfile at hdeg
    split_ifs at hdeg <;> omega
  have he := transverseSchur_coeff_recurrence H n
  rw [hconstant, hclock, zero_add] at he
  have hdeg := congrArg _root_.Polynomial.natDegree he
  change (H.a.coeff n * _root_.Polynomial.C c).natDegree = _ at hdeg
  rw [_root_.Polynomial.natDegree_mul_C hc] at hdeg
  exact hdeg.trans_le ((_root_.Polynomial.natDegree_sub_le _ _).trans (max_le hM hsum))

end TimeDegreeInduction




/-- The transported leading transverse Hessian has degree at most
two, by multiplying the exact transport equation by the polynomial
inverse pencil. No division by the reference determinant is used. -/
theorem sourceNilpotent_leadingHessian_timeDegree_le
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (L : StationarySource K)
    (hgrad : ∀ i : Fin 3, linearLineEval a N (pderiv (.inr i) L) =
      _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L)))
    (i j : Fin 3) :
    (linearLineEval a N (hessian L (.inr i) (.inr j))).natDegree ≤ 2 := by
  classical
  let H := (hessian L).submatrix Sum.inr Sum.inr
  let T := (linearLineEval a N).toRingHom.mapMatrix H
  let M := (referenceSlice a).toRingHom.mapMatrix H
  have h : T * sourceTimePencil N = M.map _root_.Polynomial.C :=
    transverseHessian_transport_of_linear_gradient a N L hgrad
  have he : T = M.map _root_.Polynomial.C * sourceTimePencilInv N := by
    calc
      T = T * (sourceTimePencil N * sourceTimePencilInv N) := by
        rw [sourceTimePencil_right_inverse N hN, mul_one]
      _ = (T * sourceTimePencil N) * sourceTimePencilInv N := (mul_assoc _ _ _).symm
      _ = _ := by rw [h]
  change (T i j).natDegree ≤ 2
  rw [he, Matrix.mul_apply]
  apply sourceTime_natDegree_sum_le
  intro k _
  change (_root_.Polynomial.C (M i k) * sourceTimePencilInv N k j).natDegree ≤ 2
  exact (_root_.Polynomial.natDegree_C_mul_le _ _).trans
    (sourceTimePencilInv_natDegree_le N k j)

/-- All six transverse coefficients are entries of the actual evaluated
source Hessian. Package their common bound for the induction. -/
private theorem sourceLinear_frame_transverse_degree
    (F : StationarySource K) (m j : ℕ) (hj : j ≤ m)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (d : ℕ)
    (hd : ∀ i k : Fin 3, (linearLineEval a N
      (hessian (initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F)
        (.inr i) (.inr k))).natDegree ≤ d) :
    let B := MvPolynomial (Fin 3) K
    let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
    let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
    let H := sourceLeading_lineSchurFrame F m z V
    (H.d.coeff j).natDegree ≤ d ∧ (H.r.coeff j).natDegree ≤ d ∧
    (H.s.coeff j).natDegree ≤ d ∧ (H.x.coeff j).natDegree ≤ d ∧
    (H.y.coeff j).natDegree ≤ d ∧ (H.z.coeff j).natDegree ≤ d := by
  let B := MvPolynomial (Fin 3) K
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
  let H := sourceLeading_lineSchurFrame F m z V
  let Q := initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F
  have he := sourceLeading_lineSchurFrame_coeff F m j hj z V
  have h00 : H.d.coeff j = linearLineEval a N (hessian Q (.inr 0) (.inr 0)) :=
    congrArg GeneralFourBlock.d he
  have h01 : H.r.coeff j = linearLineEval a N (hessian Q (.inr 0) (.inr 1)) :=
    congrArg GeneralFourBlock.r he
  have h02 : H.s.coeff j = linearLineEval a N (hessian Q (.inr 0) (.inr 2)) :=
    congrArg GeneralFourBlock.s he
  have h11 : H.x.coeff j = linearLineEval a N (hessian Q (.inr 1) (.inr 1)) :=
    congrArg GeneralFourBlock.x he
  have h12 : H.y.coeff j = linearLineEval a N (hessian Q (.inr 1) (.inr 2)) :=
    congrArg GeneralFourBlock.y he
  have h22 : H.z.coeff j = linearLineEval a N (hessian Q (.inr 2) (.inr 2)) :=
    congrArg GeneralFourBlock.z he
  change (H.d.coeff j).natDegree ≤ d ∧ (H.r.coeff j).natDegree ≤ d ∧
    (H.s.coeff j).natDegree ≤ d ∧ (H.x.coeff j).natDegree ≤ d ∧
    (H.y.coeff j).natDegree ≤ d ∧ (H.z.coeff j).natDegree ≤ d
  rw [h00, h01, h02, h11, h12, h22]
  exact ⟨hd 0 0, hd 0 1, hd 0 2, hd 1 1, hd 1 2, hd 2 2⟩

/-- Uniform degree control of every positive-order actual source layer
in a regular nilpotent linear characteristic chart. The determinant
clock and leading transport are the only source hypotheses used.
The estimate is independent of the original longitudinal degree. -/
theorem sourceNilpotent_allCorrections_timeDegree_le
    (F : StationarySource K) (m : ℕ) (hm : 3 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (hreg : referenceSlice a
      ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)) =
        _root_.Polynomial.C (referenceSlice a
          (pderiv i (initialForm transverseCubicWeight (m : ℤ) F))))
    (j : ℕ) (hj : j ≤ m) (hjpos : 0 < j) :
    (linearLineEval a N (initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F)).natDegree
      ≤ 9*j-8 := by
  classical
  let B := MvPolynomial (Fin 3) K
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
  let L := initialForm transverseCubicWeight (m : ℤ) F
  let Q := fun i : ℕ => initialForm transverseCubicWeight ((m : ℤ)-(i : ℤ)) F
  let P := fun i : ℕ => linearLineEval a N (Q i)
  let H := sourceLeading_lineSchurFrame F m z V
  let c := referenceSlice a ((hessian L).submatrix Sum.inr Sum.inr).det
  have hV : V (.inl ()) = 1 := rfl
  have hz : MvPolynomial.aeval z ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0 := hreg
  have hg : ∀ i, lineEval z V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval z (pderiv i L)) := hgrad
  have ht : ∀ i : Fin 3, linearLineEval a N (pderiv (.inr i) L) =
      _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L)) := fun i => hgrad (.inr i)
  obtain ⟨hb0, hp0, hq0, hregular⟩ :=
    sourceLeading_lineSchurFrame_kernel_regular F m z V hV hz hg
  have hclock (i : ℕ) (hi : i ≤ m) : H.determinantCore.coeff i = 0 := by
    change (sourceLeading_lineSchurFrame F m z V).determinantCore.coeff i = 0
    rw [sourceLeading_lineSchurFrame_det F m (by omega) hcap hdet,
      _root_.Polynomial.coeff_monomial, if_neg (by omega : 4*m-6 ≠ i)]
  obtain ⟨ha0, ha1⟩ := transverseSchur_longitudinal_zero_one H hb0 hp0 hq0
    hregular (hclock 0 (by omega)) (hclock 1 (by omega))
  have hconstant : (transverseSchurDet H).coeff 0 = _root_.Polynomial.C c := by
    change (transverseSchurDet (sourceLeading_lineSchurFrame F m z V)).coeff 0 = _
    rw [sourceLeading_lineSchurFrame_transverseDet_zero]
    change (linearLineEval a N).toRingHom ((hessian L).submatrix Sum.inr Sum.inr).det = _
    rw [RingHom.map_det]
    exact (sourceLinear_leadingAdjugate_transport a N L hreg ht).1
  have hdiff (i : ℕ) (hi : i ≤ m) :
      H.a.coeff i = (P i).derivative.derivative ∧
      H.b.coeff i = (linearLineEval a N (pderiv (.inr 0) (Q i))).derivative ∧
      H.p.coeff i = (linearLineEval a N (pderiv (.inr 1) (Q i))).derivative ∧
      H.q.coeff i = (linearLineEval a N (pderiv (.inr 2) (Q i))).derivative :=
    sourceLeading_lineSchurFrame_differential_coeff F m i hi z V hV
  have hbase : (P 1).natDegree ≤ 1 := by
    have he : P 1 = _root_.Polynomial.C ((P 1).coeff 0) +
        _root_.Polynomial.C ((P 1).coeff 1) * _root_.Polynomial.X :=
      sourceNilpotent_firstCorrection_affine F (m : ℤ) (by omega) hcap hdet a N hreg hgrad
    calc
      _ = (_root_.Polynomial.C ((P 1).coeff 0) +
          _root_.Polynomial.C ((P 1).coeff 1) * _root_.Polynomial.X).natDegree :=
        congrArg _root_.Polynomial.natDegree he
      _ ≤ 1 := _root_.Polynomial.natDegree_add_le_of_degree_le (by simp)
        ((_root_.Polynomial.natDegree_C_mul_le _ _).trans (by simp))
  have hlead (i k : Fin 3) :
      (linearLineEval a N (hessian (Q 0) (.inr i) (.inr k))).natDegree ≤ 2 := by
    simpa only [Q, Nat.cast_zero, sub_zero] using
      sourceNilpotent_leadingHessian_timeDegree_le a N hN L ht i k
  have hmain (n : ℕ) : n ≤ m → 0 < n → (P n).natDegree ≤ 9*n-8 := by
    induction n using Nat.strong_induction_on with
    | h n ih =>
      intro hn hpos
      by_cases hone : n = 1
      · subst n
        exact hbase
      have htwo : 2 ≤ n := by omega
      have hprev (i : ℕ) (hi : i < n) (hip : 0 < i) :
          (P i).natDegree ≤ 9*i-8 := ih i hi (by omega) hip
      have ha (i : ℕ) (hi : i < n) (hip : 2 ≤ i) :
          (H.a.coeff i).natDegree ≤ 9*i-10 := by
        rw [(hdiff i (by omega)).1]
        have h1 := _root_.Polynomial.natDegree_derivative_le (P i)
        have h2 := _root_.Polynomial.natDegree_derivative_le (P i).derivative
        have h3 := hprev i hi (by omega)
        omega
      have hmixed (i : ℕ) (hi : i < n) (hip : 0 < i) (k : Fin 3) :
          (linearLineEval a N (pderiv (.inr k) (Q i))).derivative.natDegree ≤ 9*i-7 := by
        have he := sourceNilpotent_mixed_timeDegree_le a N hN (Q i) k
        change _ ≤ (P i).natDegree + 1 at he
        have hp := hprev i hi hip
        omega
      have htrans (i : ℕ) (hi : i < n) :
          (H.d.coeff i).natDegree ≤ timeTransverseProfile i ∧
          (H.r.coeff i).natDegree ≤ timeTransverseProfile i ∧
          (H.s.coeff i).natDegree ≤ timeTransverseProfile i ∧
          (H.x.coeff i).natDegree ≤ timeTransverseProfile i ∧
          (H.y.coeff i).natDegree ≤ timeTransverseProfile i ∧
          (H.z.coeff i).natDegree ≤ timeTransverseProfile i := by
        apply sourceLinear_frame_transverse_degree F m i (by omega) a N
        intro k l
        change (linearLineEval a N (hessian (Q i) (.inr k) (.inr l))).natDegree ≤ _
        by_cases hi0 : i = 0
        · subst i
          simpa only [timeTransverseProfile, if_pos rfl] using hlead k l
        · have he := sourceNilpotent_transverseHessian_timeDegree_le a N hN (Q i) k l
          change _ ≤ (P i).natDegree + 4 at he
          have hp := hprev i hi (by omega)
          simp only [timeTransverseProfile, if_neg hi0]
          omega
      have hb (i : ℕ) (hi : i < n) (hip : 0 < i) :
          (H.b.coeff i).natDegree ≤ 9*i-7 := by
        rw [(hdiff i (by omega)).2.1]
        exact hmixed i hi hip 0
      have hp (i : ℕ) (hi : i < n) (hip : 0 < i) :
          (H.p.coeff i).natDegree ≤ 9*i-7 := by
        rw [(hdiff i (by omega)).2.2.1]
        exact hmixed i hi hip 1
      have hq (i : ℕ) (hi : i < n) (hip : 0 < i) :
          (H.q.coeff i).natDegree ≤ 9*i-7 := by
        rw [(hdiff i (by omega)).2.2.2]
        exact hmixed i hi hip 2
      have hd := transverseSchur_cleared_timeDegree_step H n htwo c hreg hconstant
        (hclock n hn) ha0 ha1 hb0 hp0 hq0 ha hb hp hq
        (fun i hi => (htrans i hi).1)
        (fun i hi => (htrans i hi).2.1)
        (fun i hi => (htrans i hi).2.2.1)
        (fun i hi => (htrans i hi).2.2.2.1)
        (fun i hi => (htrans i hi).2.2.2.2.1)
        (fun i hi => (htrans i hi).2.2.2.2.2)
      rw [(hdiff n hn).1] at hd
      have hlast := sourceTime_degree_of_secondDerivative_le (P n) (9*n-10) hd
      omega
  exact hmain j hj hjpos




/-! ## Return to original coordinates -/

theorem sourceTotalDegree_sum_le
    {σ I : Type*} (s : Finset I) (f : I → MvPolynomial σ K)
    (d : ℕ) (h : ∀ i ∈ s, (f i).totalDegree ≤ d) :
    (∑ i ∈ s, f i).totalDegree ≤ d :=
  (MvPolynomial.totalDegree_finset_sum s f).trans (Finset.sup_le h)

private theorem sourceTime_referenceCoeff_mul
    (P Q : LineTime K) (d e : ℕ)
    (hp : ∀ k, (P.coeff k).totalDegree ≤ d)
    (hq : ∀ k, (Q.coeff k).totalDegree ≤ e) :
    ∀ k, ((P*Q).coeff k).totalDegree ≤ d+e := by
  intro k
  rw [_root_.Polynomial.coeff_mul]
  apply sourceTotalDegree_sum_le
  intro ij _
  exact (MvPolynomial.totalDegree_mul _ _).trans (Nat.add_le_add (hp ij.1) (hq ij.2))

private theorem sourceTime_referenceCoeff_pow
    (P : LineTime K) (d : ℕ) (hp : ∀ k, (P.coeff k).totalDegree ≤ d)
    (n : ℕ) : ∀ k, ((P^n).coeff k).totalDegree ≤ n*d := by
  induction n with
  | zero =>
    intro k
    simp only [pow_zero, zero_mul, _root_.Polynomial.coeff_one]
    split_ifs <;> simp
  | succ n ih =>
    rw [pow_succ, Nat.succ_mul]
    exact sourceTime_referenceCoeff_mul _ _ _ _ ih hp

private theorem sourceTime_referenceCoeff_prod
    {I : Type*} (s : Finset I) (f : I → LineTime K) (d : I → ℕ)
    (h : ∀ i ∈ s, ∀ k, ((f i).coeff k).totalDegree ≤ d i) :
    ∀ k, ((∏ i ∈ s, f i).coeff k).totalDegree ≤ ∑ i ∈ s, d i := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    intro k
    simp only [Finset.prod_empty, Finset.sum_empty, _root_.Polynomial.coeff_one]
    split_ifs <;> simp
  | @insert i s hi ih =>
    rw [Finset.prod_insert hi, Finset.sum_insert hi]
    exact sourceTime_referenceCoeff_mul _ _ _ _
      (h i (Finset.mem_insert_self i s))
      (ih (fun j hj => h j (Finset.mem_insert_of_mem hj)))

private theorem sourceLinearVector_totalDegree_le
    (N : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    (sourceLinearVector N i).totalDegree ≤ 1 := by
  unfold sourceLinearVector
  apply sourceTotalDegree_sum_le
  intro j _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

private theorem referenceLinearVector_totalDegree_le
    (N : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    (referenceLinearVector N i).totalDegree ≤ 1 := by
  unfold referenceLinearVector
  apply sourceTotalDegree_sum_le
  intro j _
  exact (MvPolynomial.totalDegree_mul _ _).trans (by simp)

private def sourceTransverseNatGrade : Unit ⊕ Fin 3 → ℕ :=
  Sum.elim (fun _ => 0) (fun _ => 1)

theorem sourceTransverseNatGrade_sum (d : StationaryExponent) :
    ((∑ i ∈ d.support, d i * sourceTransverseNatGrade i : ℕ) : ℤ) =
      Finsupp.weight transverseCubicWeight d := by
  rw [Finsupp.weight_apply, Finsupp.sum]
  push_cast
  apply Finset.sum_congr rfl
  intro i _
  cases i with
  | inl u => cases u; simp [sourceTransverseNatGrade, transverseCubicWeight]
  | inr j => simp [sourceTransverseNatGrade, transverseCubicWeight, nsmul_eq_mul]

private theorem sourceTime_referenceCoeff_X
    (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (i : Unit ⊕ Fin 3) (k : ℕ) :
    ((linearLineEval a N (X i)).coeff k).totalDegree ≤ sourceTransverseNatGrade i := by
  cases i with
  | inl u =>
    cases u
    have he : linearLineEval a N (X (.inl ())) =
        _root_.Polynomial.C (MvPolynomial.C a : MvPolynomial (Fin 3) K) +
          _root_.Polynomial.X := by simp [linearLineEval, lineEval]
    rw [he, _root_.Polynomial.coeff_add, _root_.Polynomial.coeff_C, _root_.Polynomial.coeff_X]
    split_ifs <;> simp [sourceTransverseNatGrade] <;> omega
  | inr i =>
    have he : linearLineEval a N (X (.inr i)) =
        _root_.Polynomial.C (X i : MvPolynomial (Fin 3) K) +
          _root_.Polynomial.C (referenceLinearVector N i) * _root_.Polynomial.X := by
      simp [linearLineEval, lineEval, referenceLinearVector]
    rw [he, _root_.Polynomial.coeff_add, _root_.Polynomial.coeff_C,
      _root_.Polynomial.coeff_C_mul, _root_.Polynomial.coeff_X]
    have h := referenceLinearVector_totalDegree_le N i
    split_ifs <;> simp_all [sourceTransverseNatGrade]

/-- The time coefficients of a transverse homogeneous source layer
have reference total degree at most the original transverse grade. -/
theorem sourceLinear_referenceCoeff_totalDegree_le
    (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (Q : StationarySource K) (r : ℕ)
    (hQ : IsWeightLE transverseCubicWeight (r : ℤ) Q) (k : ℕ) :
    ((linearLineEval a N Q).coeff k).totalDegree ≤ r := by
  classical
  calc
    _ = ((linearLineEval a N (∑ d ∈ Q.support,
      MvPolynomial.monomial d (MvPolynomial.coeff d Q))).coeff k).totalDegree :=
        congrArg (fun P => ((linearLineEval a N P).coeff k).totalDegree) (MvPolynomial.as_sum Q)
    _ ≤ r := by
      rw [map_sum, _root_.Polynomial.finset_sum_coeff]
      apply sourceTotalDegree_sum_le
      intro d hd
      have hweight := hQ hd
      have hsum := sourceTransverseNatGrade_sum d
      have hbound : (∑ i ∈ d.support, d i * sourceTransverseNatGrade i) ≤ r := by omega
      rw [MvPolynomial.monomial_eq, map_mul]
      change ((linearLineEval a N (MvPolynomial.C (MvPolynomial.coeff d Q)) *
        linearLineEval a N (∏ i ∈ d.support, X i ^ d i)).coeff k).totalDegree ≤ r
      simp only [map_prod, map_pow]
      have hc : linearLineEval a N (MvPolynomial.C (MvPolynomial.coeff d Q)) =
          _root_.Polynomial.C (MvPolynomial.C (MvPolynomial.coeff d Q)) := by
        simp [linearLineEval, lineEval]
      rw [hc, _root_.Polynomial.coeff_C_mul]
      have hp := sourceTime_referenceCoeff_prod d.support
        (fun i => linearLineEval a N (X i) ^ d i)
        (fun i => d i * sourceTransverseNatGrade i)
        (fun i _ => sourceTime_referenceCoeff_pow _ _
          (sourceTime_referenceCoeff_X a N i) (d i)) k
      exact (MvPolynomial.totalDegree_mul _ _).trans (by
        rw [MvPolynomial.totalDegree_C, zero_add]
        exact hp.trans hbound)

private theorem sourceTime_shift_totalDegree_le (a : K) :
    (X (.inl ()) - MvPolynomial.C a : StationarySource K).totalDegree ≤ 1 := by
  rw [sub_eq_add_neg, ← map_neg]
  exact (MvPolynomial.totalDegree_add _ _).trans (by simp)

private theorem sourceNilpotentInverseEval_X_degree_le
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (i : Fin 3) :
    (sourceNilpotentInverseEval a N (X i)).totalDegree ≤ 3 := by
  rw [sourceNilpotentInverseEval, MvPolynomial.aeval_X]
  let t : StationarySource K := X (.inl ()) - MvPolynomial.C a
  change ((X (Sum.inr i : Unit ⊕ Fin 3) : StationarySource K) - t * sourceLinearVector N i +
    t^2 * sourceLinearVector (N^2) i).totalDegree ≤ 3
  have ht := sourceTime_shift_totalDegree_le a
  have h1 := (MvPolynomial.totalDegree_mul t (sourceLinearVector N i)).trans
    (Nat.add_le_add ht (sourceLinearVector_totalDegree_le N i))
  have h2 := (MvPolynomial.totalDegree_pow t 2).trans (Nat.mul_le_mul_left 2 ht)
  have h3 := (MvPolynomial.totalDegree_mul (t^2) (sourceLinearVector (N^2) i)).trans
    (Nat.add_le_add h2 (sourceLinearVector_totalDegree_le (N^2) i))
  have hn : (-(t * sourceLinearVector N i)).totalDegree ≤ 2 := by
    rw [← neg_one_mul]
    exact (MvPolynomial.totalDegree_mul _ _).trans (by simpa using h1)
  rw [sub_eq_add_neg]
  exact (MvPolynomial.totalDegree_add _ _).trans
    (max_le ((MvPolynomial.totalDegree_add _ _).trans (max_le (by simp) (hn.trans (by omega))))
      (h3.trans (by omega)))

/-- Inverse characteristic substitution increases reference total
degree by at most a factor of three. -/
theorem sourceNilpotentInverseEval_totalDegree_le
    (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (P : MvPolynomial (Fin 3) K) :
    (sourceNilpotentInverseEval a N P).totalDegree ≤ 3*P.totalDegree := by
  classical
  calc
    _ = (sourceNilpotentInverseEval a N (∑ d ∈ P.support,
      MvPolynomial.monomial d (MvPolynomial.coeff d P))).totalDegree :=
        congrArg (fun p => (sourceNilpotentInverseEval a N p).totalDegree) (MvPolynomial.as_sum P)
    _ ≤ _ := by
      rw [map_sum]
      apply sourceTotalDegree_sum_le
      intro d hd
      rw [MvPolynomial.monomial_eq, map_mul]
      change (sourceNilpotentInverseEval a N (MvPolynomial.C (MvPolynomial.coeff d P)) *
        sourceNilpotentInverseEval a N (∏ i ∈ d.support, X i ^ d i)).totalDegree ≤ _
      simp only [map_prod, map_pow]
      rw [show sourceNilpotentInverseEval a N (MvPolynomial.C (MvPolynomial.coeff d P)) =
        MvPolynomial.C (MvPolynomial.coeff d P) by simp [sourceNilpotentInverseEval]]
      apply (MvPolynomial.totalDegree_mul _ _).trans
      rw [MvPolynomial.totalDegree_C, zero_add]
      apply (MvPolynomial.totalDegree_finset_prod _ _).trans
      calc
        _ ≤ ∑ i ∈ d.support, d i * 3 := by
          apply Finset.sum_le_sum
          intro i _
          exact (MvPolynomial.totalDegree_pow _ _).trans
            (Nat.mul_le_mul_left _ (sourceNilpotentInverseEval_X_degree_le a N i))
        _ = 3 * d.sum (fun _ e => e) := by
          rw [Finsupp.sum, Finset.mul_sum]
          apply Finset.sum_congr rfl
          intro i _
          exact mul_comm _ _
        _ ≤ _ := Nat.mul_le_mul_left _ (MvPolynomial.le_totalDegree hd)

/-- Reconstruction in every time degree, not just the first correction. -/
theorem sourceNilpotent_inverseFormula
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (Q : StationarySource K) :
    let P := linearLineEval a N Q
    Q = ∑ k ∈ P.support, sourceNilpotentInverseEval a N (P.coeff k) *
      (X (.inl ()) - MvPolynomial.C a)^k := by
  let P := linearLineEval a N Q
  apply linearLineEval_injective_of_cube_zero a N hN
  simp only [map_sum, map_mul, map_pow, sourceNilpotentInverseEval_transport a N hN,
    sourceNilpotent_time_eval]
  exact (_root_.Polynomial.sum_C_mul_X_pow_eq P).symm

set_option maxHeartbeats 1000000 in
/-- A transverse cap and a time-degree cap in the nilpotent chart
give a bound on the ORIGINAL polynomial, with no determinant change. -/
theorem sourceNilpotent_originalDegree_le
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (Q : StationarySource K) (r d : ℕ)
    (hQ : IsWeightLE transverseCubicWeight (r : ℤ) Q)
    (hP : (linearLineEval a N Q).natDegree ≤ d) :
    Q.totalDegree ≤ 3*r+d := by
  let P := linearLineEval a N Q
  have he := sourceNilpotent_inverseFormula a N hN Q
  let t : StationarySource K := X (.inl ()) - MvPolynomial.C a
  change Q = ∑ k ∈ P.support, sourceNilpotentInverseEval a N (P.coeff k) * t^k at he
  calc
    _ = (∑ k ∈ P.support, sourceNilpotentInverseEval a N (P.coeff k) * t^k).totalDegree :=
        congrArg MvPolynomial.totalDegree he
    _ ≤ _ := by
      apply sourceTotalDegree_sum_le
      intro k hk
      have hk' := (_root_.Polynomial.le_natDegree_of_ne_zero (_root_.Polynomial.mem_support_iff.mp hk)).trans hP
      have hc := sourceLinear_referenceCoeff_totalDegree_le a N Q r hQ k
      have h1 := (sourceNilpotentInverseEval_totalDegree_le a N (P.coeff k)).trans
        (Nat.mul_le_mul_left 3 hc)
      have h2 := (MvPolynomial.totalDegree_pow t k).trans
        (Nat.mul_le_mul_left k (sourceTime_shift_totalDegree_le a))
      exact (MvPolynomial.totalDegree_mul _ _).trans
        (Nat.add_le_add h1 (h2.trans (by simpa using hk')))




/-- A global original-coordinate total-degree bound for a regular
nilpotent linear characteristic of an actual constant-Hessian source.
No longitudinal degree bound is an input. -/
theorem sourceNilpotent_totalDegree_le
    (F : StationarySource K) (m : ℕ) (hm : 3 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight (m : ℤ) F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ)
    (a : K) (N : Matrix (Fin 3) (Fin 3) K) (hN : N ^ 3 = 0)
    (hreg : referenceSlice a
      ((hessian (initialForm transverseCubicWeight (m : ℤ) F)).submatrix
        Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Unit ⊕ Fin 3,
      linearLineEval a N (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)) =
        _root_.Polynomial.C (referenceSlice a
          (pderiv i (initialForm transverseCubicWeight (m : ℤ) F)))) :
    F.totalDegree ≤ 9*m-8 := by
  classical
  let B := MvPolynomial (Fin 3) K
  let z : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let V : Unit ⊕ Fin 3 → B := Sum.elim (fun _ => 1) (referenceLinearVector N)
  let L := initialForm transverseCubicWeight (m : ℤ) F
  have hlead : (linearLineEval a N L).derivative.derivative = 0 := by
    change (lineEval z V L).derivative.derivative = 0
    rw [transverse_lineEval_derivative]
    have hg : ∀ i, lineEval z V (pderiv i L) =
        _root_.Polynomial.C (referenceSlice a (pderiv i L)) := hgrad
    rw [_root_.Polynomial.derivative_sum]
    apply Finset.sum_eq_zero
    intro i _
    rw [hg i]
    have he : (_root_.Polynomial.C (V i) : LineTime K) *
        _root_.Polynomial.C (referenceSlice a (pderiv i L)) =
        _root_.Polynomial.C (V i * referenceSlice a (pderiv i L)) :=
      (_root_.Polynomial.C.map_mul (V i) (referenceSlice a (pderiv i L))).symm
    calc
      _ = (_root_.Polynomial.C (V i * referenceSlice a (pderiv i L)) :
          LineTime K).derivative :=
        congrArg _root_.Polynomial.derivative he
      _ = 0 := _root_.Polynomial.derivative_C
  have hleadDegree : (linearLineEval a N L).natDegree ≤ 2 :=
    sourceTime_degree_of_secondDerivative_le _ 0 (by rw [hlead]; simp)
  have hsum := sourceLeading_reverseLayerSum_eq F m hcap
  calc
    _ = (∑ j ∈ Finset.range (m+1),
      initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F).totalDegree :=
        congrArg MvPolynomial.totalDegree hsum.symm
    _ ≤ _ := by
      apply sourceTotalDegree_sum_le
      intro j hj
      have hjm : j ≤ m := by
        have hh := Finset.mem_range.mp hj
        omega
      let Q := initialForm transverseCubicWeight ((m : ℤ)-(j : ℤ)) F
      have hQ : IsWeightLE transverseCubicWeight ((m-j : ℕ) : ℤ) Q := by
        intro d hd
        have he := initialForm_isWeightedHomogeneous transverseCubicWeight
          ((m : ℤ)-(j : ℤ)) F (MvPolynomial.mem_support_iff.mp hd)
        rw [Nat.cast_sub hjm]
        exact he.le
      by_cases hj0 : j = 0
      · subst j
        have hh : Q = L := by simp [Q, L]
        have hP : (linearLineEval a N Q).natDegree ≤ 2 := by rw [hh]; exact hleadDegree
        have hd := sourceNilpotent_originalDegree_le a N hN Q (m-0) 2 hQ hP
        exact hd.trans (by omega)
      · have hP := sourceNilpotent_allCorrections_timeDegree_le F m hm hcap hdet
          a N hN hreg hgrad j hjm (by omega)
        have hd := sourceNilpotent_originalDegree_le a N hN Q (m-j) (9*j-8) hQ hP
        exact hd.trans (by omega)

end
end HC4.Polynomial.RankThreeCubic
