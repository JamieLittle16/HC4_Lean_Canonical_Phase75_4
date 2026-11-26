import HC4.Polynomial.TransverseLeadingRationalRigidity
import HC4.Polynomial.RankThreeCubicDetOneFullAdjugateKernelRankTwo

/-!
# The four-variable singular Hessian apex without a distinguished anchor

A nonzero adjugate of a singular symmetric matrix over a domain
has a surviving principal cofactor. Use the existing kernel-coordinate
lemma rather than a new generic rank theorem. A permutation of the
original variables moves that cofactor into the distinguished
longitudinal coordinate of the complete anchored rigidity theorem.

The resulting constant annihilator is pulled back to the original
polynomial. The adjugate-zero branch is immediate. No assumption
on the original transverse block remains.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

/-- Nonzero adjugate of a singular symmetric matrix supplies a
nonzero principal cofactor, over the original domain. -/
theorem singular_symmetric_exists_principalCofactor
    {R ι : Type*} [CommRing R] [IsDomain R] [Fintype ι] [DecidableEq ι]
    (A : Matrix ι ι R) (hs : A.IsSymm) (hd : A.det = 0)
    (hn : A.adjugate ≠ 0) :
    ∃ i, A.adjugate i i ≠ 0 := by
  classical
  have hex : ∃ i j, A.adjugate i j ≠ 0 := by
    by_contra h
    push_neg at h
    apply hn
    apply Matrix.ext
    intro i j
    exact h i j
  obtain ⟨i, j, hij⟩ := hex
  let z : ι → R := fun k => A.adjugate k j
  have hz : z ≠ 0 := by
    intro h
    exact hij (congrFun h i)
  have hmul : A * A.adjugate = 0 := by
    rw [Matrix.mul_adjugate, hd, zero_smul]
  have hker : A *ᵥ z = 0 := by
    funext k
    exact congrArg (fun M : Matrix ι ι R => M k j) hmul
  have hsym : A.adjugate.IsSymm := by
    change A.adjugate.transpose = A.adjugate
    rw [Matrix.adjugate_transpose, hs]
  refine ⟨j, ?_⟩
  intro hj
  have h := adjugate_entry_zero_of_nonzero_kernel_coordinate_zero A z hker hz j i hj
  exact hij ((hsym.apply j i).trans h)

variable {K : Type*} [Field K] [CharZero K]

private abbrev I := Unit ⊕ Fin 3
private abbrev S (K : Type*) [Field K] := MvPolynomial I K

/-- Hessian renaming is simultaneous row-column reindexing and
renaming of coefficients. -/
theorem singularHessian_rename
    (e : I ≃ I) (L : S K) :
    hessian (rename e.symm L) =
      ((hessian L).submatrix e e).map (rename e.symm).toRingHom := by
  apply Matrix.ext
  intro i j
  change pderiv j (pderiv i (rename e.symm L)) =
    rename e.symm (pderiv (e j) (pderiv (e i) L))
  have hi := pderiv_rename e.symm.injective (e i) L
  have hj := pderiv_rename e.symm.injective (e j) (pderiv (e i) L)
  rw [e.symm_apply_apply] at hi hj
  rw [hi, hj]

set_option maxHeartbeats 3000000 in
/-- Four-variable singular Hessian apex: the original polynomial
adjugate always has a nonzero constant annihilator. This includes
adjugate-zero sources and arbitrary placement of a regular minor. -/
theorem singularHessian_exists_constant_adjugate_annihilator
    (L : S K) (hdet : (hessian L).det = 0) :
    ∃ d : I → K, d ≠ 0 ∧
      (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
  classical
  let H := hessian L
  by_cases hzero : H.adjugate = 0
  · refine ⟨fun _ => 1, ?_, ?_⟩
    · intro h
      exact one_ne_zero (congrFun h (.inl ()))
    · change H.adjugate *ᵥ _ = 0
      rw [hzero, Matrix.zero_mulVec]
  have hs : H.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    change pderiv i (pderiv j L) = pderiv j (pderiv i L)
    rw [HC4.Newton.pderiv_comm_backport]
  obtain ⟨k, hk⟩ := singular_symmetric_exists_principalCofactor H hs hdet hzero
  let e : I ≃ I := Equiv.swap (.inl ()) k
  let f := (rename e.symm : S K →ₐ[K] S K)
  let L' := f L
  have he : e (.inl ()) = k := by simp [e]
  have hf : Function.Injective f := by
    intro p q h
    have hh := congrArg (rename e : S K →ₐ[K] S K) h
    change rename e (rename e.symm p) = rename e (rename e.symm q) at hh
    have hid : (fun i : I => e (e.symm i)) = id := funext e.apply_symm_apply
    simpa only [rename_rename, Function.comp_def, hid, rename_id] using hh
  have hH : hessian L' = (H.submatrix e e).map f.toRingHom :=
    singularHessian_rename e L
  have hd' : (hessian L').det = 0 := by
    rw [hH]
    change (f.toRingHom.mapMatrix (H.submatrix e e)).det = 0
    rw [← RingHom.map_det, Matrix.det_submatrix_equiv_self, show H.det = 0 from hdet, map_zero]
  have hadj : (hessian L').adjugate = (H.adjugate.submatrix e e).map f.toRingHom := by
    rw [hH]
    change (f.toRingHom.mapMatrix (H.submatrix e e)).adjugate =
      f.toRingHom.mapMatrix (H.adjugate.submatrix e e)
    rw [← f.toRingHom.map_adjugate, Matrix.adjugate_submatrix_equiv_self]
  have htrans : ((hessian L').submatrix Sum.inr Sum.inr).det ≠ 0 := by
    rw [← longitudinal_principalCofactor_eq_transverseDet, hadj]
    change f (H.adjugate (e (.inl ())) (e (.inl ()))) ≠ 0
    rw [he]
    intro h
    apply hk
    apply hf
    simpa only [map_zero] using h
  obtain ⟨d, hd, hann⟩ :=
    rationalCharacteristic_adjugate_annihilator_of_transverseDet_ne_zero L' hd' htrans
  let b : I → K := fun i => d (e.symm i)
  refine ⟨b, ?_, ?_⟩
  · intro h
    apply hd
    funext i
    have hi := congrFun h (e i)
    change d (e.symm (e i)) = 0 at hi
    rwa [e.symm_apply_apply] at hi
  · funext i
    apply hf
    have hh := congrFun hann (e.symm i)
    rw [hadj] at hh
    change (∑ j : I, f (H.adjugate (e (e.symm i)) (e j)) *
      MvPolynomial.C (d j)) = 0 at hh
    simp only [e.apply_symm_apply] at hh
    change f (∑ j : I, H.adjugate i j * MvPolynomial.C (b j)) = f 0
    rw [map_zero, map_sum]
    simp only [map_mul]
    have hC (c : K) : f (MvPolynomial.C c) = MvPolynomial.C c := by
      simp [f]
    simp only [hC]
    have hsum := e.sum_comp (fun j : I => f (H.adjugate i j) * MvPolynomial.C (b j))
    change (∑ j : I, f (H.adjugate i (e j)) * MvPolynomial.C (d (e.symm (e j)))) =
      (∑ j : I, f (H.adjugate i j) * MvPolynomial.C (b j)) at hsum
    simp only [e.symm_apply_apply] at hsum
    rw [← hsum]
    exact hh

/-- The leading transverse layer now needs no regular-block
hypothesis at all. The permutation is internal to the singular
Hessian theorem and does not alter the original weight filtration. -/
theorem transverseLeading_unconditional_adjugate_annihilator
    (F : S K) (m : ℤ) (hm : 2 ≤ m)
    (hcap : IsWeightLE transverseCubicWeight m F)
    {δ : K} (hdet : hessianDeterminant F = MvPolynomial.C δ) :
    let L := initialForm transverseCubicWeight m F
    ∃ d : I → K, d ≠ 0 ∧
      (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0 :=
  singularHessian_exists_constant_adjugate_annihilator _
    (transverseLeading_hessian_det_eq_zero F m hm hcap hdet)

end
end HC4.Polynomial.RankThreeCubic

#print axioms HC4.Polynomial.RankThreeCubic.singularHessian_exists_constant_adjugate_annihilator
#print axioms HC4.Polynomial.RankThreeCubic.transverseLeading_unconditional_adjugate_annihilator
