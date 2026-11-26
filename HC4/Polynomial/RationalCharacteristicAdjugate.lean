module

public import HC4.Polynomial.RationalCharacteristicSelfAdjoint

/-!
# Constant annihilators of the Hessian along a rational characteristic

A constant vector orthogonal to the normalized rational velocity
annihilates the source adjugate after characteristic substitution.
The transverse block is invertible over the polynomial time ring
by the determinant-one transport identity.

The final pullback theorem explicitly takes injectivity of the anchored
rational substitution as input. It does not assume the affine dependence
classification, nor assert that substitution injectivity has been proved here.
-/

public section

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

abbrev RationalCharacteristicAdjugate.I := Unit ⊕ Fin 3

open RationalCharacteristicAdjugate (I)

/-- The longitudinal principal cofactor is exactly the transverse
determinant, in the actual sum-indexed matrix (without a change of frame). -/
theorem longitudinal_principalCofactor_eq_transverseDet
    {R : Type*} [CommRing R]
    (A : Matrix (Unit ⊕ Fin 3) (Unit ⊕ Fin 3) R) :
    A.adjugate (.inl ()) (.inl ()) =
      (A.submatrix Sum.inr Sum.inr).det := by
  classical
  let B := A.updateRow (.inl ()) (Pi.single (.inl ()) (1 : R))
  have hB : B = Matrix.fromBlocks
      (1 : Matrix Unit Unit R) (0 : Matrix Unit (Fin 3) R)
      (A.submatrix Sum.inr Sum.inl) (A.submatrix Sum.inr Sum.inr) := by
    ext i j
    cases i with
    | inl u =>
      cases u
      cases j with
      | inl v => cases v; simp [B, Matrix.updateRow_apply, Matrix.one_apply]
      | inr v => simp [B, Matrix.updateRow_apply, Pi.single_apply]
    | inr i =>
      cases j <;> simp [B, Matrix.updateRow_apply]
  rw [Matrix.adjugate_apply]
  change B.det = _
  rw [hB, Matrix.det_fromBlocks_zero₁₂, Matrix.det_one, one_mul]


section KernelAlgebra

variable {R : Type*} [CommRing R]

/-- A symmetric matrix whose columns lie in the normalized kernel is
annihilated by every vector orthogonal to that kernel. -/
theorem symmetric_kernelColumns_mulVec_eq_zero
    (A B : Matrix I I R) (v d : I → R)
    (hreg : IsUnit (A.submatrix Sum.inr Sum.inr).det)
    (hv : v (.inl ()) = 1) (hk : A *ᵥ v = 0)
    (hAB : A * B = 0) (hs : B.transpose = B)
    (hd : ∑ i : I, d i * v i = 0) :
    B *ᵥ d = 0 := by
  classical
  have hcol (j : I) : A *ᵥ (fun i => B i j) = 0 := by
    funext i
    have h := congrArg (fun M : Matrix I I R => M i j) hAB
    simpa only [Matrix.mul_apply, Matrix.mulVec, dotProduct, Matrix.zero_apply,
      Pi.zero_apply] using h
  have hform (j : I) : (fun i => B i j) = B (.inl ()) j • v := by
    apply sub_eq_zero.mp
    apply eq_zero_of_transverseKernel A hreg
    · simp [hv]
    · rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hcol, hk, smul_zero, sub_zero]
  funext i
  change (∑ j : I, B i j * d j) = 0
  have hb (j : I) : B i j = B (.inl ()) i * v j := by
    have hsym := congrArg (fun M : Matrix I I R => M i j) hs
    change B j i = B i j at hsym
    rw [← hsym]
    exact congrFun (hform i) j
  simp_rw [hb, mul_assoc, mul_comm (v _) (d _)]
  rw [← Finset.mul_sum, hd, mul_zero]

end KernelAlgebra

variable {K : Type*} [Field K]

/-- Differentiation in characteristic time is the directional derivative
of the original polynomial, evaluated by the same affine substitution. -/
theorem transverse_lineEval_derivative
    {ι E : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing E] [Algebra K E]
    (z V : ι → E) (P : MvPolynomial ι K) :
    (lineEval z V P).derivative =
      ∑ i : ι, _root_.Polynomial.C (V i) * lineEval z V (pderiv i P) := by
  classical
  let e := lineEval (K := K) z V
  have hprod (p q : MvPolynomial ι K) :
      (∑ i : ι, _root_.Polynomial.C (V i) * e (pderiv i (p * q))) =
        e p * (∑ i : ι, _root_.Polynomial.C (V i) * e (pderiv i q)) +
        e q * (∑ i : ι, _root_.Polynomial.C (V i) * e (pderiv i p)) := by
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro i _
    rw [Derivation.leibniz]
    simp only [smul_eq_mul, map_add, map_mul]
    ring
  change (e P).derivative = _
  induction P using MvPolynomial.induction_on with
  | C a =>
    rw [show e (MvPolynomial.C a) =
        _root_.Polynomial.C (algebraMap K E a) by
      simp [e, lineEval, IsScalarTower.algebraMap_apply K E (_root_.Polynomial E),
        _root_.Polynomial.algebraMap_eq]]
    simp [e]
  | add p q hp hq =>
    simp only [map_add, _root_.Polynomial.derivative_add, hp, hq,
      mul_add, Finset.sum_add_distrib]
  | mul_X p i hp =>
    have hx : (e (X i)).derivative =
        ∑ j : ι, _root_.Polynomial.C (V j) * e (pderiv j (X i)) := by
      rw [show e (X i) = _root_.Polynomial.C (z i) +
          _root_.Polynomial.C (V i) * _root_.Polynomial.X by
        simp [e, lineEval]]
      rw [Finset.sum_eq_single i]
      · simp [pderiv_X]
      · intro j _ hji
        simp [pderiv_X, hji, Ne.symm hji]
      · simp
    change (e (p * X i)).derivative =
      ∑ j : ι, _root_.Polynomial.C (V j) * e (pderiv j (p * X i))
    rw [hprod, map_mul, _root_.Polynomial.derivative_mul, hp, hx]
    ring


namespace RationalCharacteristicAdjugate

abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
abbrev E (K : Type*) [Field K] := FractionRing (B K)
abbrev S (K : Type*) [Field K] := MvPolynomial I K

end RationalCharacteristicAdjugate

open RationalCharacteristicAdjugate (B E S)

/-- The actual Hessian has the normalized characteristic in its kernel
at every polynomial time, not merely at the reference point. -/
theorem rationalCharacteristic_allTime_kernel
    (a : K) (L : S K) (V : I → E K)
    (hgrad : ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L))) :
    ((lineEval (transverseGenericPoint a) V).toRingHom.mapMatrix (hessian L)) *ᵥ
      (fun i => _root_.Polynomial.C (V i)) = 0 := by
  classical
  funext i
  have h := transverse_lineEval_derivative (transverseGenericPoint a) V (pderiv i L)
  rw [hgrad i, _root_.Polynomial.derivative_C] at h
  change (∑ j : I, lineEval (transverseGenericPoint a) V
    (pderiv j (pderiv i L)) * _root_.Polynomial.C (V j)) = 0
  simpa only [mul_comm] using h.symm

/-- The full transverse determinant stays a unit throughout the
rational characteristic. This uses the source-derived transport pencil. -/
theorem rationalCharacteristic_allTime_transverse_isUnit
    (a : K) (L : S K) (V : I → E K)
    (hV : V (.inl ()) = 1)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L))) :
    IsUnit (((lineEval (transverseGenericPoint a) V).toRingHom.mapMatrix
      (hessian L)).submatrix Sum.inr Sum.inr).det := by
  classical
  let H := (hessian L).submatrix Sum.inr Sum.inr
  let T := (lineEval (transverseGenericPoint a) V).toRingHom.mapMatrix H
  let M := (MvPolynomial.aeval (transverseGenericPoint a)).toRingHom.mapMatrix H
  let J : Matrix (Fin 3) (Fin 3) (_root_.Polynomial (E K)) :=
    1 + (_root_.Polynomial.X : _root_.Polynomial (E K)) •
      (rationalCharacteristicJacobian V).map _root_.Polynomial.C
  have ht := transverseHessian_transport_of_rational_gradient a L V hV
    (fun i => hgrad (.inr i))
  change T * J = M.map _root_.Polynomial.C at ht
  have hj : J.det = 1 :=
    det_rationalCharacteristic_eq_one a L V hV hreg (fun i => hgrad (.inr i))
  have hh : T.det * J.det = _root_.Polynomial.C
      (MvPolynomial.aeval (transverseGenericPoint a) H.det) := by
    rw [← Matrix.det_mul, ht]
    exact (_root_.Polynomial.C.map_det M).symm.trans
      (congrArg _root_.Polynomial.C
        ((MvPolynomial.aeval (transverseGenericPoint a)).map_det H).symm)
  rw [hj, mul_one] at hh
  change IsUnit T.det
  rw [hh]
  exact (isUnit_iff_ne_zero.mpr hreg).map _root_.Polynomial.C

variable [CharZero K]

/-- A constant annihilator of the characteristic velocity annihilates
the actual source adjugate along the whole characteristic. -/
theorem rationalCharacteristic_adjugate_annihilator_along_line
    (a : K) (L : S K) (V : I → E K) (d : I → K)
    (hdet : (hessian L).det = 0)
    (hV : V (.inl ()) = 1)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L)))
    (hd : ∑ i : I, algebraMap K (E K) (d i) * V i = 0) :
    ((lineEval (transverseGenericPoint a) V).toRingHom.mapMatrix (hessian L).adjugate) *ᵥ
      (fun i => _root_.Polynomial.C (algebraMap K (E K) (d i))) = 0 := by
  classical
  let e := lineEval (K := K) (transverseGenericPoint a) V
  let H := hessian L
  let A := e.toRingHom.mapMatrix H
  let Q := e.toRingHom.mapMatrix H.adjugate
  have hH : H.transpose = H := by
    ext i j
    simp only [H, Matrix.transpose_apply, hessian_apply]
    rw [HC4.Newton.pderiv_comm_backport]
  have hsym : Q.transpose = Q := by
    have hs : H.adjugate.transpose = H.adjugate := by
      rw [Matrix.adjugate_transpose, hH]
    apply Matrix.ext
    intro i j
    exact congrArg e (congrArg (fun M : Matrix I I (S K) => M i j) hs)
  have hmul : H * H.adjugate = 0 := by
    rw [Matrix.mul_adjugate, show H.det = 0 from hdet]
    simp
  have hAQ : A * Q = 0 := by
    change H.map e.toRingHom * H.adjugate.map e.toRingHom = 0
    rw [← Matrix.map_mul, hmul]
    ext i j
    simp
  have hd' : ∑ i : I, _root_.Polynomial.C (algebraMap K (E K) (d i)) *
      _root_.Polynomial.C (V i) = 0 := by
    simpa only [map_sum, map_mul, map_zero] using congrArg _root_.Polynomial.C hd
  exact symmetric_kernelColumns_mulVec_eq_zero A Q
    (fun i => _root_.Polynomial.C (V i))
    (fun i => _root_.Polynomial.C (algebraMap K (E K) (d i)))
    (rationalCharacteristic_allTime_transverse_isUnit a L V hV hreg hgrad)
    (by simp [hV]) (rationalCharacteristic_allTime_kernel a L V hgrad)
    hAQ hsym hd'

/-- The algebraic apex bridge, conditional only on the explicitly stated
injectivity of the anchored rational substitution. The velocity
annihilator must be supplied, not inferred from nilpotence alone. -/
theorem rationalCharacteristic_adjugate_annihilator_of_injective
    (a : K) (L : S K) (V : I → E K) (d : I → K)
    (hdet : (hessian L).det = 0)
    (hV : V (.inl ()) = 1)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L)))
    (hd : ∑ i : I, algebraMap K (E K) (d i) * V i = 0)
    (hinj : Function.Injective
      (lineEval (K := K) (transverseGenericPoint a) V)) :
    (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
  classical
  let e := lineEval (K := K) (transverseGenericPoint a) V
  have h := rationalCharacteristic_adjugate_annihilator_along_line
    a L V d hdet hV hreg hgrad hd
  funext i
  apply hinj
  change e (∑ j : I, (hessian L).adjugate i j * MvPolynomial.C (d j)) = e 0
  rw [map_zero, map_sum]
  simp only [map_mul]
  have hc (r : K) : e (MvPolynomial.C r) =
      _root_.Polynomial.C (algebraMap K (E K) r) := by
    simp [e, lineEval, IsScalarTower.algebraMap_apply K (E K)
      (_root_.Polynomial (E K)), _root_.Polynomial.algebraMap_eq]
  simp_rw [hc]
  exact congrFun h i

end
end HC4.Polynomial.RankThreeCubic
