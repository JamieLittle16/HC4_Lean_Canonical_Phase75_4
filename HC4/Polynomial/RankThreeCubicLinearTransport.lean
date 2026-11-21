import HC4.Polynomial.RankThreeCubicJordanSquare
import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff

/-!
# Differentiated transport of a linear characteristic

Differentiate the transported gradient in the original transverse
indeterminates, keeping characteristic time fixed. This produces
the Hessian transport equation and forces the constant velocity
matrix to be nilpotent.
-/

namespace HC4.Polynomial.RankThreeCubic
open MvPolynomial
open scoped BigOperators Matrix

noncomputable section

section ChainRule

variable {K A ι : Type*} [CommRing K] [CommRing A] [Algebra K A]
  [Fintype ι] [DecidableEq ι]

/-- The coordinate chain rule for a derivation of the target. -/
theorem derivation_aeval (D : Derivation K A A) (z : ι → A) (p : MvPolynomial ι K) :
    D (MvPolynomial.aeval z p) = ∑ i, MvPolynomial.aeval z (pderiv i p) * D (z i) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [Derivation.map_algebraMap]
  | add p q hp hq => simp [map_add, hp, hq, add_mul, Finset.sum_add_distrib]
  | mul_X p j hp =>
    let E : MvPolynomial ι K →ₐ[K] A := MvPolynomial.aeval z
    change D (E (p * X j)) = ∑ i, E (pderiv i (p * X j)) * D (z i)
    have hx : E (X j) = z j := MvPolynomial.aeval_X z j
    have he : ∑ i, (E p * E (pderiv i (X j : MvPolynomial ι K))) * D (z i) = E p * D (z j) := by
      rw [Finset.sum_eq_single j]
      · simp
      · intro i _ hi
        rw [pderiv_X_of_ne (Ne.symm hi), map_zero, mul_zero, zero_mul]
      · simp
    simp only [map_mul, Derivation.leibniz, smul_eq_mul, hx, map_add, add_mul]
    rw [Finset.sum_add_distrib, he]
    simp_rw [mul_assoc]
    rw [← Finset.mul_sum, ← hp]

end ChainRule

section PolynomialCoefficients

variable {K A : Type*} [CommRing K] [CommRing A] [Algebra K A]

@[simp]
theorem coeffDeriv_C (D : Derivation K A A) (a : A) :
    coeffDeriv D (_root_.Polynomial.C a) = _root_.Polynomial.C (D a) := by
  ext n
  simp [coeff_coeffDeriv, _root_.Polynomial.coeff_C, apply_ite D]

@[simp]
theorem coeffDeriv_X (D : Derivation K A A) :
    coeffDeriv D (_root_.Polynomial.X : _root_.Polynomial A) = 0 := by
  ext n
  simp [coeff_coeffDeriv, _root_.Polynomial.coeff_X, apply_ite D, Derivation.map_one_eq_zero]

end PolynomialCoefficients

section LinearTransport

variable {K ι : Type*} [Field K] [Fintype ι] [DecidableEq ι]

local notation "B" => MvPolynomial ι K
local notation "S" => MvPolynomial (Unit ⊕ ι) K

/-- The reference slice at the longitudinal ground-field point. -/
def referenceSlice (a : K) : S →ₐ[K] B :=
  MvPolynomial.aeval (Sum.elim (fun _ : Unit => MvPolynomial.C a) X)

/-- Characteristics with a given constant linear transverse velocity. -/
def linearLineEval (a : K) (N : Matrix ι ι K) : S →ₐ[K] _root_.Polynomial B :=
  lineEval (Sum.elim (fun _ => MvPolynomial.C a) X)
    (Sum.elim (fun _ => 1) (fun i => ∑ j, MvPolynomial.C (N i j) * X j))

/-- Taking a transverse derivative commutes with restricting the
longitudinal coordinate to a constant. -/
theorem referenceSlice_pderiv (a : K) (j : ι) (p : S) :
    pderiv j (referenceSlice a p) = referenceSlice a (pderiv (.inr j) p) := by
  classical
  unfold referenceSlice
  rw [derivation_aeval]
  simp only [Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    pderiv_C, mul_zero, Finset.sum_const_zero, zero_add]
  rw [Finset.sum_eq_single j]
  · simp
  · intro i _ hi
    rw [pderiv_X_of_ne hi, mul_zero]
  · simp

/-- In the constant linear chart, the transverse Hessian transport
follows from the gradient transport, not from a separate hypothesis. -/
theorem transverseHessian_transport_of_linear_gradient
    (a : K) (N : Matrix ι ι K) (L : S)
    (hgrad : ∀ i : ι, linearLineEval a N (pderiv (.inr i) L) =
      _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L))) :
    let H := (hessian L).submatrix Sum.inr Sum.inr
    let T := (linearLineEval a N).toRingHom.mapMatrix H
    let M := (referenceSlice a).toRingHom.mapMatrix H
    T * (1 + (_root_.Polynomial.X : _root_.Polynomial B) •
      (N.map MvPolynomial.C).map _root_.Polynomial.C) =
        M.map _root_.Polynomial.C := by
  classical
  dsimp
  let z : Unit ⊕ ι → B := Sum.elim (fun _ => MvPolynomial.C a) X
  let v : Unit ⊕ ι → B :=
    Sum.elim (fun _ => 1) (fun i => ∑ j, MvPolynomial.C (N i j) * X j)
  let w : Unit ⊕ ι → _root_.Polynomial B := fun i =>
    _root_.Polynomial.C (z i) + _root_.Polynomial.C (v i) * _root_.Polynomial.X
  have hE : linearLineEval a N = MvPolynomial.aeval w := rfl
  have hz (j k : ι) : pderiv j (z (.inr k)) = if k = j then 1 else 0 := by
    by_cases h : k = j
    · subst k; simp [z]
    · simp [z, h, pderiv_X_of_ne h]
  have hv (j k : ι) : pderiv j (v (.inr k)) = MvPolynomial.C (N k j) := by
    simp only [v, Sum.elim_inr, map_sum, MvPolynomial.pderiv_C_mul]
    rw [Finset.sum_eq_single j]
    · simp
    · intro i _ hi
      rw [pderiv_X_of_ne hi, mul_zero]
    · simp
  have hc (j : ι) : coeffDeriv (pderiv j : Derivation K B B) (w (.inl ())) = 0 := by
    simp [w, z, v]
  let J : Matrix ι ι (_root_.Polynomial B) :=
    1 + (_root_.Polynomial.X : _root_.Polynomial B) •
      (N.map MvPolynomial.C).map _root_.Polynomial.C
  have ht (j k : ι) :
      coeffDeriv (pderiv j : Derivation K B B) (w (.inr k)) = J k j := by
    change coeffDeriv (pderiv j : Derivation K B B)
      (_root_.Polynomial.C (z (.inr k)) +
      _root_.Polynomial.C (v (.inr k)) * _root_.Polynomial.X) = _
    simp only [map_add, coeffDeriv_C, Derivation.leibniz, smul_eq_mul, coeffDeriv_X,
      mul_zero, zero_add, hz, hv, J, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.map_apply, apply_ite _root_.Polynomial.C, map_one, map_zero]
  apply Matrix.ext
  intro i j
  have e := congrArg (coeffDeriv (pderiv j : Derivation K B B)) (hgrad i)
  rw [coeffDeriv_C, referenceSlice_pderiv, hE, derivation_aeval] at e
  simp only [Fintype.sum_sum_type, hc, mul_zero, Finset.sum_const_zero, zero_add, ht] at e
  simpa only [Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.submatrix_apply,
    hessian_apply, hE, J] using e

/-- The transverse Jacobian of a linear characteristic has constant
determinant one, even before choosing Jordan coordinates. -/
theorem det_linearCharacteristic_eq_one
    (a : K) (N : Matrix ι ι K) (L : S)
    (hreg : referenceSlice a ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : ι, linearLineEval a N (pderiv (.inr i) L) =
      _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L))) :
    let J : Matrix ι ι (_root_.Polynomial K) :=
      1 + (_root_.Polynomial.X : _root_.Polynomial K) • N.map _root_.Polynomial.C
    J.det = 1 := by
  classical
  let J : Matrix ι ι (_root_.Polynomial K) :=
    1 + (_root_.Polynomial.X : _root_.Polynomial K) • N.map _root_.Polynomial.C
  let g : K →+* B := MvPolynomial.C
  let J' : Matrix ι ι (_root_.Polynomial B) :=
    1 + (_root_.Polynomial.X : _root_.Polynomial B) •
      (N.map MvPolynomial.C).map _root_.Polynomial.C
  let H := (hessian L).submatrix Sum.inr Sum.inr
  let T := (linearLineEval a N).toRingHom.mapMatrix H
  let M := (referenceSlice a).toRingHom.mapMatrix H
  have h := transverseHessian_transport_of_linear_gradient a N L hgrad
  change T * J' = _ at h
  have hh : T.det * J'.det = _root_.Polynomial.C (referenceSlice a H.det) := by
    rw [← Matrix.det_mul, h]
    exact (_root_.Polynomial.C.map_det M).symm.trans
      (congrArg _root_.Polynomial.C ((referenceSlice a).map_det H).symm)
  have hz : J'.det.coeff 0 = 1 := by
    let e := _root_.Polynomial.constantCoeff (R := B)
    have he : e.mapMatrix J' = 1 := by
      ext i j
      by_cases hij : i = j <;>
        simp [e, J', Matrix.one_apply, hij, Matrix.smul_apply, smul_eq_mul, RingHom.mapMatrix_apply]
    change e J'.det = 1
    rw [e.map_det, he, Matrix.det_one]
  have hJ' := polynomial_factor_eq_one hreg hh hz
  let f := _root_.Polynomial.mapRingHom g
  have he : f.mapMatrix J = J' := by
    ext i j
    by_cases hij : i = j <;>
      simp [f, g, J, J', hij, Matrix.smul_apply, smul_eq_mul,
        RingHom.mapMatrix_apply, _root_.Polynomial.map_add, _root_.Polynomial.map_mul]
  change J.det = 1
  apply _root_.Polynomial.map_injective g (MvPolynomial.C_injective ι K)
  change f J.det = f 1
  rw [f.map_det, he, hJ', map_one]

/-- A determinant-one characteristic pencil gives nilpotence by
reversing the characteristic polynomial and applying Cayley–Hamilton. -/
theorem matrix_pow_card_eq_zero_of_det_linear_eq_one
    (N : Matrix ι ι K)
    (h : (1 + (_root_.Polynomial.X : _root_.Polynomial K) •
      N.map _root_.Polynomial.C).det = 1) :
    N ^ Fintype.card ι = 0 := by
  let P := -N
  have hr : P.charpolyRev = 1 := by
    rw [Matrix.charpolyRev]
    have he : 1 - (_root_.Polynomial.X : _root_.Polynomial K) • P.map _root_.Polynomial.C =
        1 + (_root_.Polynomial.X : _root_.Polynomial K) • N.map _root_.Polynomial.C := by
      ext i j
      simp [P, Matrix.smul_apply, smul_eq_mul, sub_eq_add_neg]
    rw [he, h]
  have href : _root_.Polynomial.reflect (Fintype.card ι) P.charpoly = 1 := by
    rw [← Matrix.charpoly_natDegree_eq_dim P]
    exact P.reverse_charpoly.trans hr
  have hcp : P.charpoly = _root_.Polynomial.X ^ Fintype.card ι := by
    have he := congrArg (_root_.Polynomial.reflect (Fintype.card ι)) href
    rw [_root_.Polynomial.reflect_one] at he
    convert he using 1
    ext n
    simp [_root_.Polynomial.revAt_invol]
  have hz := P.aeval_self_charpoly
  rw [hcp, map_pow, _root_.Polynomial.aeval_X] at hz
  have hp : N = -P := by simp [P]
  rw [hp, neg_pow, hz, mul_zero]


end LinearTransport
end
end HC4.Polynomial.RankThreeCubic
