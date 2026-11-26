import HC4.Polynomial.RankTwoGlobalClosure

/-!
# The remaining actual rank-three extremum

The rank-at-most-two theorem is now unconditional. Here it is
combined with singularity of the weighted leading determinant and
the four-variable adjugate-annihilator theorem, in the Fin 4
coordinates used by global weight optimization. The result retains
the same full source, cap, optimum and gradient collision.

A zero cofactor column is not a constant Hessian kernel.
-/

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open scoped Matrix BigOperators
noncomputable section

section Matrix
variable {R : Type*} [CommRing R] [IsDomain R]

set_option maxHeartbeats 4000000 in
/-- Every injective three-coordinate selection is a permutation
of the complement of a single coordinate. -/
theorem threeCoordinates_eq_complement_perm :
    ∀ r : Fin 3 → Fin 4, Function.Injective r →
      ∃ (k : Fin 4) (e : Equiv.Perm (Fin 3)),
        r = fun i => k.succAbove (e i) := by
  decide

/-- At dimension four, all order-three minors vanish precisely
when the adjugate vanishes. No field extension is required. -/
theorem allThreeMinorsZero_iff_adjugate_zero
    (A : Matrix (Fin 4) (Fin 4) R) :
    AllThreeMinorsZero A ↔ A.adjugate = 0 := by
  classical
  constructor
  · intro h
    apply Matrix.ext
    intro i j
    rw [Matrix.adjugate_fin_succ_eq_det_submatrix, h j.succAbove i.succAbove, mul_zero] <;> rfl
  · intro h r c
    by_cases hr : Function.Injective r
    · by_cases hc : Function.Injective c
      · obtain ⟨j,e,he⟩ := threeCoordinates_eq_complement_perm r hr
        obtain ⟨i,f,hf⟩ := threeCoordinates_eq_complement_perm c hc
        have h0 : (A.submatrix j.succAbove i.succAbove).det = 0 := by
          have hz := congrArg (fun M : Matrix (Fin 4) (Fin 4) R => M i j) h
          change A.adjugate i j = 0 at hz
          rw [Matrix.adjugate_fin_succ_eq_det_submatrix] at hz
          exact (mul_eq_zero.mp hz).resolve_left (pow_ne_zero _ (neg_ne_zero.mpr one_ne_zero))
        rw [he,hf]
        change (((A.submatrix j.succAbove i.succAbove).submatrix e id).submatrix id f).det = 0
        rw [Matrix.det_permute',Matrix.det_permute,h0,mul_zero,mul_zero]
      · have hn : ∃ a b : Fin 3, a ≠ b ∧ c a = c b := by
          by_contra hn
          apply hc
          intro a b hab
          by_contra hne
          exact hn ⟨a,b,hne,hab⟩
        obtain ⟨a,b,hab,he⟩ := hn
        exact Matrix.det_zero_of_column_eq hab (fun i => congrArg (A (r i)) he)
    · have hn : ∃ a b : Fin 3, a ≠ b ∧ r a = r b := by
        by_contra hn
        apply hr
        intro a b hab
        by_contra hne
        exact hn ⟨a,b,hne,hab⟩
      obtain ⟨a,b,hab,he⟩ := hn
      apply Matrix.det_zero_of_row_eq hab
      funext i
      exact congrArg (fun j => A j (c i)) he

end Matrix

variable {K : Type*} [Field K] [CharZero K]
private abbrev S (K : Type*) [Field K] := MvPolynomial (Fin 4) K
private abbrev I := Unit ⊕ Fin 3

set_option maxHeartbeats 3000000 in
/-- Transport the singular Hessian annihilator theorem to Fin 4.
Only variable names change, and the original adjugate relation
is recovered by the inverse renaming. -/
theorem singularHessian_fin4_exists_constant_adjugate_annihilator
    (L : S K) (hd : (hessian L).det = 0) :
    ∃ d : Fin 4 → K, d ≠ 0 ∧
      (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0 := by
  classical
  let e : I ≃ Fin 4 := Fintype.equivOfCardEq (by decide)
  let f := (rename e.symm : S K →ₐ[K] MvPolynomial I K)
  let A := hessian L
  let Q := f L
  have hf : Function.Injective f := by
    intro p q h
    have he := congrArg (rename e : MvPolynomial I K →ₐ[K] S K) h
    change rename e (rename e.symm p) = rename e (rename e.symm q) at he
    have hid : (fun i : Fin 4 => e (e.symm i)) = id := funext e.apply_symm_apply
    simpa only [rename_rename,Function.comp_def, hid, rename_id, AlgHom.id_apply] using he
  have hQ : hessian Q = (A.submatrix e e).map f.toRingHom := by
    apply Matrix.ext
    intro i j
    change pderiv j (pderiv i (rename e.symm L)) =
      rename e.symm (pderiv (e j) (pderiv (e i) L))
    have hi := pderiv_rename e.symm.injective (e i) L
    have hj := pderiv_rename e.symm.injective (e j) (pderiv (e i) L)
    rw [e.symm_apply_apply] at hi hj
    rw [hi,hj]
  have hdetQ : (hessian Q).det = 0 := by
    rw [hQ]
    change (f.toRingHom.mapMatrix (A.submatrix e e)).det = 0
    rw [← RingHom.map_det,Matrix.det_submatrix_equiv_self,show A.det = 0 from hd,map_zero]
  have ha : (hessian Q).adjugate = (A.adjugate.submatrix e e).map f.toRingHom := by
    rw [hQ]
    change (f.toRingHom.mapMatrix (A.submatrix e e)).adjugate =
      f.toRingHom.mapMatrix (A.adjugate.submatrix e e)
    rw [← f.toRingHom.map_adjugate,Matrix.adjugate_submatrix_equiv_self]
  obtain ⟨d,hd0,hann⟩ := RankThreeCubic.singularHessian_exists_constant_adjugate_annihilator Q hdetQ
  let b : Fin 4 → K := fun i => d (e.symm i)
  refine ⟨b,?_,?_⟩
  · intro h
    apply hd0
    funext i
    have hi := congrFun h (e i)
    change d (e.symm (e i)) = 0 at hi
    rwa [e.symm_apply_apply] at hi
  · funext i
    apply hf
    have hh := congrFun hann (e.symm i)
    rw [ha] at hh
    change (∑ j : I, f (A.adjugate (e (e.symm i)) (e j)) * MvPolynomial.C (d j)) = 0 at hh
    simp only [e.apply_symm_apply] at hh
    change f (∑ j : Fin 4, A.adjugate i j * MvPolynomial.C (b j)) = f 0
    rw [map_zero,map_sum]
    simp only [map_mul]
    have hC (c : K) : f (MvPolynomial.C c) = MvPolynomial.C c := f.commutes c
    simp only [hC]
    have hsum := e.sum_comp (fun j : Fin 4 => f (A.adjugate i j) * MvPolynomial.C (b j))
    change (∑ j : I, f (A.adjugate i (e j)) * MvPolynomial.C (d (e.symm (e j)))) =
      (∑ j : Fin 4, f (A.adjugate i j) * MvPolynomial.C (b j)) at hsum
    simp only [e.symm_apply_apply] at hsum
    rw [← hsum]
    exact hh

/-- Exact rank three at every positive-clock optimal determinant-one
source, expressed by zero determinant and nonzero adjugate. -/
theorem globalWeightOptimum_rankThree
    (P : S K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ i, 0 ≤ w i) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i))
    (hopt : IsGlobalWeightOptimum P w m) (hdet : hessianDeterminant P = 1) :
    (hessian (initialForm w m P)).det = 0 ∧
      (hessian (initialForm w m P)).adjugate ≠ 0 := by
  constructor
  · change hessianDeterminant (initialForm w m P) = 0
    rw [← initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm w m P hcap,hdet]
    exact initialForm_eq_zero_of_isWeightedHomogeneous
      (MvPolynomial.isWeightedHomogeneous_one K w) _ (ne_of_gt hclock)
  · intro h
    exact globalWeightOptimum_not_rankAtMostTwo P w m hw hm hcap hclock hopt hdet
      ((allThreeMinorsZero_iff_adjugate_zero _).mpr h)

set_option maxHeartbeats 4000000 in
/-- The remaining rank-three source admits an actual weight-block
chart with a zero adjugate column and a surviving principal cofactor
at a different coordinate. The full-source cap, determinant,
optimality and collision are all preserved. -/
theorem counterexample_exists_rankThree_complementary_chart
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : S K) (hdet : hessianDeterminant P = 1)
    (hnoninj : ¬ Function.Injective (mvGradientMap P)) :
    ∃ (M : Matrix (Fin 4) (Fin 4) K) (w : Fin 4 → ℤ) (m : ℤ)
      (k l : Fin 4), M.det = 1 ∧ (∀ i, 0 ≤ w i) ∧ 0 < m ∧ k ≠ l ∧
      let Q := weightedLinearSubstitution M P
      let A := hessian (initialForm w m Q)
      IsWeightLE w m Q ∧ hessianDeterminant Q = 1 ∧
      ¬ Function.Injective (mvGradientMap Q) ∧
      0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ i, w i) ∧
      IsGlobalWeightOptimum Q w m ∧ A.det = 0 ∧
      (∀ i, A.adjugate i k = 0) ∧ A.adjugate l l ≠ 0 := by
  classical
  obtain ⟨M,w,m,hM,hw,hm,hcap,hdetQ,hnQ,hclock,hopt⟩ :=
    exists_counterexample_globalWeightOptimum hJC2 P hdet hnoninj
  let Q := weightedLinearSubstitution M P
  let L := initialForm w m Q
  have hRank := globalWeightOptimum_rankThree Q w m hw hm hcap hclock hopt hdetQ
  obtain ⟨d,hd,ha⟩ := singularHessian_fin4_exists_constant_adjugate_annihilator L hRank.1
  obtain ⟨k,hk,_⟩ := extremal_exists_topWeight_pivot w d hd
  let b : Fin 4 → K := fun i => if w i = w k then d i else 0
  have hbk : b k ≠ 0 := by simpa [b] using hk
  have hb : ∀ i, w i ≠ w k → b i = 0 := by intro i hi; simp [b,hi]
  have hba : (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (b i)) = 0 :=
    weighted_adjugate_annihilator_block w m L
      (initialForm_isWeightedHomogeneous w m Q) d ha (w k)
  let N := annihilatorShear b k
  have hN : N.det = 1 := annihilatorShear_det b k
  have hblock : ∀ i j, w i ≠ w j → N i j = 0 :=
    annihilatorShear_respects_weight w b k hb
  let Q' := weightedLinearSubstitution N Q
  have hcap' : IsWeightLE w m Q' :=
    weightedLinearSubstitution_isWeightLE w N hblock m Q hcap
  have hdet' : hessianDeterminant Q' = 1 := by
    change hessianDeterminant (weightedLinearSubstitution N Q) = 1
    rw [weightedLinearSubstitution_det N hN,hdetQ,map_one]
  have hopt' : IsGlobalWeightOptimum Q' w m := hopt.substitution N hN
  have hn' : ¬ Function.Injective (mvGradientMap Q') := by
    intro hi
    exact hnQ ((weightedLinearSubstitution_gradient_injective_iff N hN Q).mp hi)
  let A := hessian (initialForm w m Q')
  have hcol : ∀ i, A.adjugate i k = 0 := by
    intro i
    change (hessian (initialForm w m (weightedLinearSubstitution N Q))).adjugate i k = 0
    rw [weightedLinearSubstitution_initialForm w N hblock]
    exact weightedLinearSubstitution_zero_adjugate_column L b k hbk hba i
  have hRank' := globalWeightOptimum_rankThree Q' w m hw hm hcap' hclock hopt' hdet'
  have hs : A.IsSymm := by
    apply Matrix.IsSymm.ext
    intro i j
    exact pderiv_comm_backport _ _ _
  obtain ⟨l,hl⟩ := RankThreeCubic.singular_symmetric_exists_principalCofactor A hs hRank'.1 hRank'.2
  have hkl : k ≠ l := by
    intro he
    subst l
    exact hl (hcol k)
  refine ⟨M*N,w,m,k,l,by rw [Matrix.det_mul,hM,hN,mul_one],hw,hm,hkl,?_⟩
  rw [← weightedLinearSubstitution_comp]
  exact ⟨hcap',hdet',hn',hclock,hopt',hRank'.1,hcol,hl⟩

end
end HC4.Polynomial

#print axioms HC4.Polynomial.allThreeMinorsZero_iff_adjugate_zero
#print axioms HC4.Polynomial.singularHessian_fin4_exists_constant_adjugate_annihilator
#print axioms HC4.Polynomial.globalWeightOptimum_rankThree
#print axioms HC4.Polynomial.counterexample_exists_rankThree_complementary_chart
