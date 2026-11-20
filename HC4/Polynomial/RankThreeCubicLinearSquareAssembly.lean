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
    _ = (H * N) * N := by rw [← Matrix.mul_assoc, hcomm]
    _ = H * N ^ 2 := by rw [pow_two, Matrix.mul_assoc]

private theorem reference_hessian_eq_mapped_transverse
    (a : K) (L : MvPolynomial (Unit ⊕ Fin 3) K) :
    (referenceSlice a).toRingHom.mapMatrix
        ((hessian L).submatrix Sum.inr Sum.inr) =
      hessian (referenceSlice a L) := by
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.submatrix_apply, hessian_apply]
  rw [referenceSlice_pderiv a i, referenceSlice_pderiv a j]

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

/-- A nonzero nilpotent linear characteristic gives a fixed square
derivative on the original four-variable cubic grade, without
assuming an independently supplied reference square or a Jordan chart. -/
theorem exists_source_square_of_nonzero_linear_characteristic
    (a : K) (N : Matrix (Fin 3) (Fin 3) K)
    (L : MvPolynomial (Unit ⊕ Fin 3) K)
    (hNnonzero : N ≠ 0)
    (hreg : referenceSlice a
      ((hessian L).submatrix Sum.inr Sum.inr).det ≠ 0)
    (hq : (referenceSlice a L).IsHomogeneous 3)
    (hgrad : ∀ i : Fin 3,
      linearLineEval a N (pderiv (.inr i) L) =
        _root_.Polynomial.C (referenceSlice a (pderiv (.inr i) L))) :
    ∃ (d l : Fin 3 → K) (c : K),
      d ≠ 0 ∧ l ≠ 0 ∧ c ≠ 0 ∧
      N *ᵥ d = 0 ∧ l ᵥ* N = 0 ∧
      (∑ i : Fin 3,
        (MvPolynomial.C (d i) : MvPolynomial (Unit ⊕ Fin 3) K) *
          pderiv (.inr i) L) =
        MvPolynomial.C c *
          (∑ i : Fin 3,
            (MvPolynomial.C (l i) : MvPolynomial (Unit ⊕ Fin 3) K) *
              X (.inr i)) ^ 2 := by
  classical
  have hdetN := det_linearCharacteristic_eq_one a N L hreg hgrad
  have hnil := matrix_pow_card_eq_zero_of_det_linear_eq_one N hdetN
  have h3 : N ^ 3 = 0 := by simpa using hnil
  obtain ⟨r, d, l, hr, hd, hl, hfac, hNd, hlN⟩ :=
    exists_nilpotent_rankOnePower N hNnonzero h3
  let q := referenceSlice a L
  let H := hessian q
  let A := N.map (MvPolynomial.C : K →+* MvPolynomial (Fin 3) K)
  have hqdet : H.det ≠ 0 := by
    have he := congrArg Matrix.det (reference_hessian_eq_mapped_transverse a L)
    have he' : referenceSlice a
        ((hessian L).submatrix Sum.inr Sum.inr).det = H.det := by
      simpa only [← RingHom.map_det] using he
    exact he' ▸ hreg
  have hH : H.transpose = H := by
    ext i j
    simp only [Matrix.transpose_apply, H, hessian_apply]
    rw [HC4.Newton.pderiv_comm_backport]
  have hHN : (H * A).transpose = H * A :=
    reference_hessian_selfAdjoint_of_linear_transport a N L hgrad
  have hpower : (H * A ^ r).transpose = H * A ^ r := by
    rcases hr with hr | hr
    · subst r
      simpa using hHN
    · subst r
      exact symmetric_mul_square H A hH hHN
  have hfac' : A ^ r =
      Matrix.vecMulVec (fun i => MvPolynomial.C (d i))
        (fun i => MvPolynomial.C (l i)) := by
    change (N.map MvPolynomial.C) ^ r = _
    rw [← Matrix.map_pow, hfac]
    ext i j
    simp [Matrix.vecMulVec]
  have hsquare : ∀ i j : Fin 3,
      (H * Matrix.vecMulVec (fun i => MvPolynomial.C (d i))
        (fun i => MvPolynomial.C (l i))) i j =
      (H * Matrix.vecMulVec (fun i => MvPolynomial.C (d i))
        (fun i => MvPolynomial.C (l i))) j i := by
    intro i j
    rw [← hfac']
    exact (congrArg (fun M : Matrix (Fin 3) (Fin 3)
      (MvPolynomial (Fin 3) K) => M i j) hpower).symm
  obtain ⟨c, hc, hsq⟩ :=
    reference_directional_eq_square_of_rankOne q hq hqdet d l hd hl hsquare
  refine ⟨d, l, c, hd, hl, hc, hNd, hlN, ?_⟩
  exact source_square_of_linear_characteristic a N h3 L d l c
    hgrad hlN hsq

end
end HC4.Polynomial.RankThreeCubic
