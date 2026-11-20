import HC4.Polynomial.RankThreeCubicLinearSourcePullback

/-!
# Connect nilpotent linear characteristic transport to the source square

The reference Hessian self-adjointness, not an additional Jordan
assumption, supplies the final reference-square input.
-/

namespace HC4.Polynomial.RankThreeCubic
open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private theorem symmetric_mul_square
    {A : Type*} [CommRing A]
    (H N : Matrix (Fin 3) (Fin 3) A)
    (hH : H.transpose = H)
    (hHN : (H * N).transpose = H * N) :
    (H * N ^ 2).transpose = H * N ^ 2 := by
  have hcomm : N.transpose * H = H * N := by
    simpa [Matrix.transpose_mul, hH] using hHN
  calc
    (H * N ^ 2).transpose = ((H * N) * N).transpose := by rw [pow_two, Matrix.mul_assoc]
    _ = N.transpose * (H * N).transpose := by rw [Matrix.transpose_mul]
    _ = N.transpose * (H * N) := by rw [hHN]
    _ = (H * N) * N := by rw [Matrix.mul_assoc, hcomm]
    _ = H * N ^ 2 := by rw [pow_two, Matrix.mul_assoc]

private theorem reference_hessian_eq_mapped_transverse
    (a : K) (L : MvPolynomial (Unit ⊕ Fin 3) K) :
    (referenceSlice a).toRingHom.mapMatrix
        ((hessian L).submatrix Sum.inr Sum.inr) =
      hessian (referenceSlice a L) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.submatrix_apply, hessian_apply]
  rw [← referenceSlice_pderiv a j, ← referenceSlice_pderiv a i]

/-- The coefficient of the characteristic time makes the original
reference Hessian self-adjoint against the linear velocity. -/
theorem reference_hessian_selfAdjoint_of_linear_transport
    (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (L : MvPolynomial (Unit ⊕ Fin 3) K)
    (hgrad : ∀ i : Fin 3,
      linearLineEval a N (pderiv (.inr i) L) =
        _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L))) :
    let H := hessian (referenceSlice a L)
    let N' := N.map MvPolynomial.C
    (H * N').transpose = H * N' := by
  classical
  let T := (linearLineEval a N).toRingHom.mapMatrix
    ((hessian L).submatrix Sum.inr Sum.inr)
  let M := (referenceSlice a).toRingHom.mapMatrix
    ((hessian L).submatrix Sum.inr Sum.inr)
  have hs : ∀ i j, T i j = T j i := by
    intro i j
    simp only [T, RingHom.mapMatrix_apply, Matrix.submatrix_apply, hessian_apply]
    rw [HC4.Newton.pderiv_comm_backport]
  have htransport := transverseHessian_transport_of_linear_gradient a N L hgrad
  have hsym := selfAdjoint_of_linearCharacteristic T M (N.map MvPolynomial.C)
    hs htransport
  have hM : M = hessian (referenceSlice a L) :=
    reference_hessian_eq_mapped_transverse a L
  change (hessian (referenceSlice a L) * N.map MvPolynomial.C).transpose =
    hessian (referenceSlice a L) * N.map MvPolynomial.C
  apply Matrix.ext
  intro i j
  change (hessian (referenceSlice a L) * N.map MvPolynomial.C) j i =
    (hessian (referenceSlice a L) * N.map MvPolynomial.C) i j
  rw [← hM]
  exact (hsym j i)

end
end HC4.Polynomial.RankThreeCubic
