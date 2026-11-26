import HC4.Polynomial.RankThreeCubicLinearTransport
import HC4.Polynomial.RankThreeCubicSourceFractionKernel
import Mathlib.Tactic

/-!
# Rational characteristic transport and nilpotence

The differentiated characteristic identity is valid over the genuine
transverse fraction field, not only for polynomial or linear velocities.
We use the original source gradient transport to derive the determinant-one
time pencil and its nilpotent velocity Jacobian. No bound on transverse
degree and no condition on the denominator is imposed.

This is the algebraic transport part of the rational characteristic
rigidity investigation; no classification of rational nilpotent fields
is assumed.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open nonZeroDivisors
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev S (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- The original transverse partial derivative extended to the fraction field. -/
def rationalCharacteristicPartial (j : Fin 3) : Derivation K (E K) (E K) :=
  localizationDerivation (nonZeroDivisors (B K)) (pderiv j)

@[simp]
theorem rationalCharacteristicPartial_algebraMap
    (j : Fin 3) (p : B K) :
    rationalCharacteristicPartial j (algebraMap (B K) (E K) p) =
      algebraMap (B K) (E K) (pderiv j p) :=
  localizationDerivation_algebraMap (nonZeroDivisors (B K)) _ _

/-- The Jacobian of the normalized transverse velocity, with rows
indexed by velocity components and columns by original coordinates. -/
def rationalCharacteristicJacobian (V : Unit ⊕ Fin 3 → E K) :
    Matrix (Fin 3) (Fin 3) (E K) :=
  fun i j => rationalCharacteristicPartial j (V (.inr i))

/-- Differentiating an actual transported gradient in the transverse
fraction field gives the Hessian transport equation. -/
theorem transverseHessian_transport_of_rational_gradient
    (a : K) (L : S K) (V : Unit ⊕ Fin 3 → E K)
    (hV : V (.inl ()) = 1)
    (hgrad : ∀ i : Fin 3, lineEval (transverseGenericPoint a) V (pderiv (.inr i) L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv (.inr i) L))) :
    let H := (hessian L).submatrix Sum.inr Sum.inr
    let T := (lineEval (transverseGenericPoint a) V).toRingHom.mapMatrix H
    let M := (MvPolynomial.aeval (transverseGenericPoint a)).toRingHom.mapMatrix H
    T * (1 + (_root_.Polynomial.X : _root_.Polynomial (E K)) •
      (rationalCharacteristicJacobian V).map _root_.Polynomial.C) =
        M.map _root_.Polynomial.C := by
  classical
  dsimp
  let z := transverseGenericPoint a
  let D (j : Fin 3) : Derivation K (E K) (E K) := rationalCharacteristicPartial j
  let w : Unit ⊕ Fin 3 → _root_.Polynomial (E K) := fun i =>
    _root_.Polynomial.C (z i) + _root_.Polynomial.C (V i) * _root_.Polynomial.X
  let J : Matrix (Fin 3) (Fin 3) (_root_.Polynomial (E K)) :=
    1 + (_root_.Polynomial.X : _root_.Polynomial (E K)) •
      (rationalCharacteristicJacobian V).map _root_.Polynomial.C
  have hE : (lineEval (K := K) z V : S K →ₐ[K] _root_.Polynomial (E K)) =
      MvPolynomial.aeval w := rfl
  have hz (j k : Fin 3) : D j (z (.inr k)) = if k = j then 1 else 0 := by
    change rationalCharacteristicPartial j (algebraMap (B K) (E K) (X k)) = _
    rw [rationalCharacteristicPartial_algebraMap]
    by_cases h : k = j
    · subst k
      simp
    · simp [h, pderiv_X_of_ne h]
  have hza (j : Fin 3) : D j (z (.inl ())) = 0 := by
    change D j (algebraMap K (E K) a) = 0
    exact Derivation.map_algebraMap (D j) a
  have hc (j : Fin 3) : coeffDeriv (D j) (w (.inl ())) = 0 := by
    simp [w, hza, hV]
  have ht (j k : Fin 3) : coeffDeriv (D j) (w (.inr k)) = J k j := by
    change coeffDeriv (D j)
      (_root_.Polynomial.C (z (.inr k)) +
        _root_.Polynomial.C (V (.inr k)) * _root_.Polynomial.X) = _
    simp only [map_add, coeffDeriv_C, Derivation.leibniz, smul_eq_mul, coeffDeriv_X,
      mul_zero, zero_add, hz, J, Matrix.add_apply, Matrix.one_apply, Matrix.smul_apply,
      Matrix.map_apply, apply_ite _root_.Polynomial.C, map_one, map_zero]
    rfl
  have hbase (i j : Fin 3) :
      D j (MvPolynomial.aeval z (pderiv (.inr i) L)) =
        MvPolynomial.aeval z (pderiv (.inr j) (pderiv (.inr i) L)) := by
    rw [derivation_aeval]
    simp only [Fintype.sum_sum_type, hza, mul_zero, Finset.sum_const_zero, zero_add]
    rw [Finset.sum_eq_single j]
    · simp [hz]
    · intro k _ hk
      rw [hz, if_neg hk, mul_zero]
    · simp
  apply Matrix.ext
  intro i j
  have e := congrArg (coeffDeriv (D j)) (hgrad i)
  change coeffDeriv (D j) (lineEval z V (pderiv (.inr i) L)) =
    coeffDeriv (D j) (_root_.Polynomial.C (MvPolynomial.aeval z (pderiv (.inr i) L))) at e
  rw [coeffDeriv_C, hbase, hE, derivation_aeval] at e
  simp only [Fintype.sum_sum_type, hc, mul_zero, Finset.sum_const_zero, zero_add, ht] at e
  simpa only [Matrix.mul_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.submatrix_apply, hessian_apply, hE, J] using e

/-- The velocity Jacobian pencil has determinant one over the fraction
field, even when the velocity has poles. -/
theorem det_rationalCharacteristic_eq_one
    (a : K) (L : S K) (V : Unit ⊕ Fin 3 → E K)
    (hV : V (.inl ()) = 1)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Fin 3, lineEval (transverseGenericPoint a) V (pderiv (.inr i) L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv (.inr i) L))) :
    (1 + (_root_.Polynomial.X : _root_.Polynomial (E K)) •
      (rationalCharacteristicJacobian V).map _root_.Polynomial.C).det = 1 := by
  classical
  let J : Matrix (Fin 3) (Fin 3) (_root_.Polynomial (E K)) :=
    1 + (_root_.Polynomial.X : _root_.Polynomial (E K)) •
      (rationalCharacteristicJacobian V).map _root_.Polynomial.C
  let H := (hessian L).submatrix Sum.inr Sum.inr
  let T := (lineEval (transverseGenericPoint a) V).toRingHom.mapMatrix H
  let M := (MvPolynomial.aeval (transverseGenericPoint a)).toRingHom.mapMatrix H
  have h := transverseHessian_transport_of_rational_gradient a L V hV hgrad
  change T * J = M.map _root_.Polynomial.C at h
  have hh : T.det * J.det = _root_.Polynomial.C
      (MvPolynomial.aeval (transverseGenericPoint a) H.det) := by
    rw [← Matrix.det_mul, h]
    exact (_root_.Polynomial.C.map_det M).symm.trans
      (congrArg _root_.Polynomial.C
        ((MvPolynomial.aeval (transverseGenericPoint a)).map_det H).symm)
  have hz : J.det.coeff 0 = 1 := by
    let e := _root_.Polynomial.constantCoeff (R := E K)
    have he : e.mapMatrix J = 1 := by
      ext i j
      by_cases hij : i = j <;>
        simp [e, J, Matrix.one_apply, hij, Matrix.smul_apply, RingHom.mapMatrix_apply]
    change e J.det = 1
    rw [e.map_det, he, Matrix.det_one]
  exact polynomial_factor_eq_one hreg hh hz

/-- Degree-independent nilpotence of the actual rational characteristic
Jacobian. The determinant-to-nilpotence step is the existing
Cayley--Hamilton theorem over the fraction field. -/
theorem rationalCharacteristicJacobian_cube_eq_zero
    (a : K) (L : S K) (V : Unit ⊕ Fin 3 → E K)
    (hV : V (.inl ()) = 1)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hgrad : ∀ i : Fin 3, lineEval (transverseGenericPoint a) V (pderiv (.inr i) L) =
      _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv (.inr i) L))) :
    rationalCharacteristicJacobian V ^ 3 = 0 := by
  simpa using matrix_pow_card_eq_zero_of_det_linear_eq_one
    (rationalCharacteristicJacobian V) (det_rationalCharacteristic_eq_one a L V hV hreg hgrad)

/-- The existing anchored-characteristic construction now yields a
rational nilpotent Jacobian directly from a singular source Hessian. -/
theorem exists_anchored_rationalCharacteristic_nilpotent [CharZero K]
    (a : K) (L : S K) (hdet : (hessian L).det = 0)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0) :
    ∃ V : Unit ⊕ Fin 3 → E K, V (.inl ()) = 1 ∧
      (∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
        _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L))) ∧
      rationalCharacteristicJacobian V ^ 3 = 0 := by
  obtain ⟨V, hV, hg⟩ := exists_anchored_lineEval_gradient_eq L hdet (transverseGenericPoint a) hreg
  exact ⟨V, hV, hg, rationalCharacteristicJacobian_cube_eq_zero a L V hV hreg
    (fun i => hg (.inr i))⟩

end
end HC4.Polynomial.RankThreeCubic
