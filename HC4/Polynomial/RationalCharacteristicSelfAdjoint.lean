import HC4.Polynomial.RationalCharacteristicTransport
import HC4.Polynomial.RankThreeCubicPoleJacobiBridge

/-!
# Self-adjointness of rational characteristic Jacobians

The transported Hessian times the velocity Jacobian is symmetric:
subtract the symmetric transported Hessian from the transport equation
and cancel characteristic time. Specialization at time zero gives the
self-adjointness identity for the original transverse Hessian.

The symmetrizer is the Hessian of the actual polynomial reference slice.
Together with nilpotence this supplies the source-derived input for
rational characteristic rigidity, without assuming that rigidity.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K
private abbrev E (K : Type*) [Field K] := FractionRing (B K)
private abbrev S (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- The transverse Hessian at the original generic reference point. -/
def rationalCharacteristicHessian (a : K) (L : S K) :
    Matrix (Fin 3) (Fin 3) (E K) :=
  (MvPolynomial.aeval (transverseGenericPoint a)).toRingHom.mapMatrix
    ((hessian L).submatrix Sum.inr Sum.inr)

/-- The symmetrizer really is a polynomial Hessian, included into
the fraction field from the actual reference slice. -/
theorem rationalCharacteristicHessian_eq_slice_hessian
    (a : K) (L : S K) :
    rationalCharacteristicHessian a L =
      (hessian (referenceSlice a L)).map (algebraMap (B K) (E K)) := by
  ext i j
  change MvPolynomial.aeval (transverseGenericPoint a)
      (pderiv (.inr j) (pderiv (.inr i) L)) =
    algebraMap (B K) (E K)
      (pderiv j (pderiv i (referenceSlice a L)))
  rw [referenceSlice_pderiv, referenceSlice_pderiv,
    referenceSlice_fractionEvaluation]

theorem rationalCharacteristicHessian_det_ne_zero
    (a : K) (L : S K)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0) :
    (rationalCharacteristicHessian a L).det ≠ 0 := by
  change ((MvPolynomial.aeval (transverseGenericPoint a)).toRingHom.mapMatrix
    ((hessian L).submatrix Sum.inr Sum.inr)).det ≠ 0
  rw [← RingHom.map_det]
  exact hreg

/-- Self-adjointness of the velocity Jacobian follows directly from
the actual rational gradient transport. Invertibility and nilpotence
are not required for this particular identity. -/
theorem rationalCharacteristicJacobian_selfAdjoint
    (a : K) (L : S K) (V : Unit ⊕ Fin 3 → E K)
    (hV : V (.inl ()) = 1)
    (hgrad : ∀ i : Fin 3,
      lineEval (transverseGenericPoint a) V (pderiv (.inr i) L) =
        _root_.Polynomial.C
          (MvPolynomial.aeval (transverseGenericPoint a) (pderiv (.inr i) L))) :
    let M := rationalCharacteristicHessian a L
    let N := rationalCharacteristicJacobian V
    N.transpose * M = M * N := by
  classical
  let H := (hessian L).submatrix Sum.inr Sum.inr
  let T := (lineEval (transverseGenericPoint a) V).toRingHom.mapMatrix H
  let M := rationalCharacteristicHessian a L
  let N := rationalCharacteristicJacobian V
  let C := N.map _root_.Polynomial.C
  have hT (i j : Fin 3) : T i j = T j i := by
    change lineEval (transverseGenericPoint a) V
      (pderiv (.inr j) (pderiv (.inr i) L)) =
      lineEval (transverseGenericPoint a) V
        (pderiv (.inr i) (pderiv (.inr j) L))
    rw [HC4.Newton.pderiv_comm_backport]
  have hM (i j : Fin 3) : M i j = M j i := by
    change MvPolynomial.aeval (transverseGenericPoint a)
      (pderiv (.inr j) (pderiv (.inr i) L)) =
      MvPolynomial.aeval (transverseGenericPoint a)
        (pderiv (.inr i) (pderiv (.inr j) L))
    rw [HC4.Newton.pderiv_comm_backport]
  have ht := transverseHessian_transport_of_rational_gradient a L V hV hgrad
  change T * (1 + (_root_.Polynomial.X : _root_.Polynomial (E K)) • C) =
    M.map _root_.Polynomial.C at ht
  rw [Matrix.mul_add, Matrix.mul_one, Matrix.mul_smul] at ht
  have he (i j : Fin 3) :
      T i j + (_root_.Polynomial.X : _root_.Polynomial (E K)) * (T * C) i j =
        _root_.Polynomial.C (M i j) := by
    have h := congrArg (fun Q : Matrix (Fin 3) (Fin 3) (_root_.Polynomial (E K)) =>
      Q i j) ht
    exact h
  have hTC (i j : Fin 3) : (T * C) i j = (T * C) j i := by
    apply mul_left_cancel₀ (_root_.Polynomial.X_ne_zero (R := E K))
    have h₁ := he i j
    rw [hT i j, hM i j] at h₁
    exact add_left_cancel (h₁.trans (he j i).symm)
  let e := _root_.Polynomial.constantCoeff (R := E K)
  have hT0 : T.map e = M := by
    ext i j
    change (lineEval (transverseGenericPoint a) V
      (pderiv (.inr j) (pderiv (.inr i) L))).coeff 0 =
      MvPolynomial.aeval (transverseGenericPoint a)
        (pderiv (.inr j) (pderiv (.inr i) L))
    exact cubic_lineEval_coeff_zero _ _ _
  have hC0 : C.map e = N := by
    ext i j
    change (_root_.Polynomial.C (N i j)).coeff 0 = N i j
    simp
  have hprod : (T * C).map e = M * N := by
    rw [Matrix.map_mul, hT0, hC0]
  have hMt : M.transpose = M := by
    ext i j
    exact hM j i
  have hMN : (M * N).transpose = M * N := by
    ext i j
    change (M * N) j i = (M * N) i j
    rw [← hprod]
    exact congrArg e (hTC j i)
  change N.transpose * M = M * N
  calc
    N.transpose * M = (M * N).transpose := by
      rw [Matrix.transpose_mul, hMt]
    _ = M * N := hMN

/-- Source-derived nilpotence and a generically nonsingular polynomial
Hessian symmetrizer, with no transverse degree or pole restriction. -/
theorem exists_anchored_rationalCharacteristic_rigidityInput
    (a : K) (L : S K) (hdet : (hessian L).det = 0)
    (hreg : MvPolynomial.aeval (transverseGenericPoint a)
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0) :
    ∃ V : Unit ⊕ Fin 3 → E K, V (.inl ()) = 1 ∧
      (∀ i, lineEval (transverseGenericPoint a) V (pderiv i L) =
        _root_.Polynomial.C (MvPolynomial.aeval (transverseGenericPoint a) (pderiv i L))) ∧
      rationalCharacteristicJacobian V ^ 3 = 0 ∧
      (rationalCharacteristicHessian a L).det ≠ 0 ∧
      (rationalCharacteristicJacobian V).transpose * rationalCharacteristicHessian a L =
        rationalCharacteristicHessian a L * rationalCharacteristicJacobian V := by
  obtain ⟨V, hV, hg, hn⟩ :=
    exists_anchored_rationalCharacteristic_nilpotent a L hdet hreg
  exact ⟨V, hV, hg, hn, rationalCharacteristicHessian_det_ne_zero a L hreg,
    rationalCharacteristicJacobian_selfAdjoint a L V hV (fun i => hg (.inr i))⟩

end
end HC4.Polynomial.RankThreeCubic
