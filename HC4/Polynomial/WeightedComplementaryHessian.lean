import HC4.Polynomial.WeightedSingularHessianAnnihilator

/-!
# A weight-compatible complementary Hessian

A nonzero constant adjugate annihilator supported in one weight
block can be aligned with a coordinate by a determinant-one shear.
The actual polynomial Hessian transforms by congruence, so the
corresponding adjugate column vanishes identically.

This is not a claim that the direction is in the Hessian kernel,
nor that the potential is independent of that coordinate.
-/

namespace HC4.Polynomial

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

section Linear

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- The shear aligning a covector d at a nonzero pivot k. -/
def annihilatorShear (d : ι → K) (k : ι) : Matrix ι ι K :=
  (1 : Matrix ι ι K).updateRow k
    (fun j => if j = k then 1 else -(d j / d k))

theorem annihilatorShear_det (d : ι → K) (k : ι) :
    (annihilatorShear d k).det = 1 := by
  classical
  let r : ι → K := fun j => if j = k then 1 else -(d j / d k)
  have hr : (∑ j : ι, r j • (1 : Matrix ι ι K) j) = r := by
    funext i
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Matrix.one_apply]
    rw [Finset.sum_eq_single i]
    · simp
    · intro j _ hj
      simp [hj]
    · simp
  change ((1 : Matrix ι ι K).updateRow k r).det = 1
  have he := Matrix.det_updateRow_sum (1 : Matrix ι ι K) k r
  rw [hr, Matrix.det_one] at he
  simpa [r] using he

/-- The shear does not mix coordinates of distinct weights. -/
theorem annihilatorShear_respects_weight
    (w : ι → ℤ) (d : ι → K) (k : ι)
    (hd : ∀ j, w j ≠ w k → d j = 0) :
    ∀ i j, w i ≠ w j → annihilatorShear d k i j = 0 := by
  classical
  intro i j hij
  by_cases hi : i = k
  · subst i
    have hj : j ≠ k := by
      intro h
      apply hij
      rw [h]
    have hz : d j = 0 := hd j (Ne.symm hij)
    simp [annihilatorShear, Matrix.updateRow_apply, hj, hz]
  · have hne : i ≠ j := by
      intro h
      apply hij
      rw [h]
    simp [annihilatorShear, Matrix.updateRow_apply, hi, Matrix.one_apply, hne]

/-- The transformed covector is concentrated at the selected pivot. -/
theorem annihilatorShear_transpose_mulVec
    (d : ι → K) (k : ι) (hk : d k ≠ 0) :
    (annihilatorShear d k).transpose *ᵥ d = d k • (Pi.single k (1 : K) : ι → K) := by
  classical
  let M := annihilatorShear d k
  funext j
  change (∑ i : ι, M i j * d i) = d k * Pi.single k (1 : K) j
  by_cases hj : j = k
  · subst j
    rw [Finset.sum_eq_single k]
    · simp [M, annihilatorShear, Matrix.updateRow_apply]
    · intro i _ hi
      simp [M, annihilatorShear, Matrix.updateRow_apply, hi, Matrix.one_apply]
    · simp
  · have hs (i : ι) : M i j * d i =
        (if i = k then -(d j / d k) * d k else 0) +
        (if i = j then d j else 0) := by
      by_cases hi : i = k
      · subst i
        simp [M, annihilatorShear, Matrix.updateRow_apply, hj, Ne.symm hj]
      · by_cases hij : i = j
        · subst i
          simp [M, annihilatorShear, Matrix.updateRow_apply, hj, Matrix.one_apply]
        · simp [M, annihilatorShear, Matrix.updateRow_apply, hi, hij, Matrix.one_apply]
    simp only [hs, Finset.sum_add_distrib]
    have hsum (a : ι) (c : K) :
        (∑ i : ι, if i = a then c else 0) = c := by
      rw [Finset.sum_eq_single a]
      · simp
      · intro i _ hi
        simp [hi]
      · simp
    rw [hsum, hsum, neg_mul, div_mul_cancel₀ _ hk, neg_add_cancel]
    simp [Pi.single_apply, hj]

/-- Congruence by the shear sends a constant adjugate annihilator
to a zero column, even before imposing any Hessian structure. -/
theorem adjugate_congruence_zero_column
    {R : Type*} [CommRing R] [IsDomain R]
    (A M : Matrix ι ι R) (d : ι → R) (k : ι) (c : R)
    (hc : c ≠ 0) (hM : M.det = 1)
    (hd : A.adjugate *ᵥ d = 0)
    (hcol : M.transpose *ᵥ d = c • (Pi.single k (1 : R) : ι → R)) :
    ∀ i, (M.transpose * A * M).adjugate i k = 0 := by
  classical
  have hdet : M.transpose.det = 1 := by rw [Matrix.det_transpose, hM]
  have ht : M.transpose.adjugate *ᵥ (M.transpose *ᵥ d) = d := by
    rw [Matrix.mulVec_mulVec, Matrix.adjugate_mul, hdet, one_smul, Matrix.one_mulVec]
  have hz : (M.transpose * A * M).adjugate *ᵥ (M.transpose *ᵥ d) = 0 := by
    rw [Matrix.adjugate_mul_distrib, Matrix.adjugate_mul_distrib]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ht, hd, Matrix.mulVec_zero]
  rw [hcol, Matrix.mulVec_smul, Matrix.mulVec_single_one] at hz
  intro i
  have hi := congrFun hz i
  change c * (M.transpose * A * M).adjugate i k = 0 at hi
  exact (mul_eq_zero.mp hi).resolve_left hc

end Linear

section Polynomial

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

/-- Actual linear substitution on the original polynomial ring. -/
def weightedLinearSubstitution (M : Matrix ι ι K) :
    MvPolynomial ι K →ₐ[K] MvPolynomial ι K :=
  MvPolynomial.aeval (fun i => ∑ j : ι, MvPolynomial.C (M i j) * X j)

theorem weightedLinearSubstitution_X_partial
    (M : Matrix ι ι K) (i j : ι) :
    pderiv j (weightedLinearSubstitution M (X i)) = MvPolynomial.C (M i j) := by
  classical
  unfold weightedLinearSubstitution
  rw [MvPolynomial.aeval_X, map_sum]
  simp only [MvPolynomial.pderiv_C_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [pderiv_X_of_ne hk, mul_zero]
  · simp

theorem weightedLinearSubstitution_partial
    (M : Matrix ι ι K) (f : MvPolynomial ι K) (j : ι) :
    pderiv j (weightedLinearSubstitution M f) =
      ∑ i : ι, weightedLinearSubstitution M (pderiv i f) * MvPolynomial.C (M i j) := by
  let z : ι → MvPolynomial ι K := fun i => ∑ j : ι, MvPolynomial.C (M i j) * X j
  change pderiv j (MvPolynomial.aeval z f) =
    ∑ i : ι, MvPolynomial.aeval z (pderiv i f) * MvPolynomial.C (M i j)
  rw [RankThreeCubic.derivation_aeval]
  apply Finset.sum_congr rfl
  intro i _
  have he := weightedLinearSubstitution_X_partial M i j
  change pderiv j (MvPolynomial.aeval z (X i)) = MvPolynomial.C (M i j) at he
  rw [MvPolynomial.aeval_X] at he
  rw [he]

/-- Genuine arbitrary-degree Hessian congruence. -/
theorem weightedLinearSubstitution_hessian
    (M : Matrix ι ι K) (f : MvPolynomial ι K) :
    hessian (weightedLinearSubstitution M f) =
      (M.map (MvPolynomial.C : K →+* MvPolynomial ι K)).transpose *
      (hessian f).map (weightedLinearSubstitution M).toRingHom *
      M.map (MvPolynomial.C : K →+* MvPolynomial ι K) := by
  classical
  apply Matrix.ext
  intro i j
  simp only [hessian_apply]
  rw [weightedLinearSubstitution_partial M f i, map_sum]
  simp only [Derivation.leibniz, smul_eq_mul, pderiv_C, mul_zero, zero_add]
  simp only [weightedLinearSubstitution_partial, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.map_apply, hessian_apply]
  change (∑ a : ι, MvPolynomial.C (M a i) *
      (∑ b : ι, weightedLinearSubstitution M (pderiv b (pderiv a f)) *
        MvPolynomial.C (M b j))) =
    ∑ b : ι, (∑ a : ι, MvPolynomial.C (M a i) *
      weightedLinearSubstitution M (pderiv b (pderiv a f))) * MvPolynomial.C (M b j)
  simp only [Finset.mul_sum, Finset.sum_mul, mul_assoc]
  exact Finset.sum_comm

/-- Constant Hessian determinant is unchanged by a determinant-one
linear substitution. -/
theorem weightedLinearSubstitution_det
    (M : Matrix ι ι K) (hM : M.det = 1)
    (f : MvPolynomial ι K) :
    hessianDeterminant (weightedLinearSubstitution M f) =
      weightedLinearSubstitution M (hessianDeterminant f) := by
  unfold hessianDeterminant
  rw [weightedLinearSubstitution_hessian, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose]
  change ((MvPolynomial.C : K →+* MvPolynomial ι K).mapMatrix M).det *
    ((weightedLinearSubstitution M).toRingHom.mapMatrix (hessian f)).det *
    ((MvPolynomial.C : K →+* MvPolynomial ι K).mapMatrix M).det = _
  rw [← RingHom.map_det, ← RingHom.map_det, hM, map_one, one_mul, mul_one] <;> rfl

/-- Annihilator alignment on the actual substituted potential. -/
theorem weightedLinearSubstitution_zero_adjugate_column
    (L : MvPolynomial ι K) (d : ι → K) (k : ι) (hk : d k ≠ 0)
    (hd : (hessian L).adjugate *ᵥ (fun i => MvPolynomial.C (d i)) = 0) :
    ∀ i, (hessian (weightedLinearSubstitution (annihilatorShear d k) L)).adjugate i k = 0 := by
  classical
  let M := annihilatorShear d k
  let f := weightedLinearSubstitution M
  let C : K →+* MvPolynomial ι K := MvPolynomial.C
  let A := (hessian L).map f.toRingHom
  let T := M.map C
  let b : ι → MvPolynomial ι K := fun i => C (d i)
  have hT : T.det = 1 := by
    change (C.mapMatrix M).det = 1
    rw [← RingHom.map_det, annihilatorShear_det, map_one]
  have hAb : A.adjugate *ᵥ b = 0 := by
    have he : A.adjugate = (hessian L).adjugate.map f.toRingHom :=
      (f.toRingHom.map_adjugate (hessian L)).symm
    rw [he]
    funext i
    have hh := congrArg f (congrFun hd i)
    change f (∑ j : ι, (hessian L).adjugate i j * C (d j)) = f 0 at hh
    have hC (a : K) : f (C a) = C a := by
      exact f.commutes a
    simp only [map_sum, map_mul, map_zero, hC] at hh
    exact hh
  have ht : T.transpose *ᵥ b = C (d k) • (Pi.single k (1 : MvPolynomial ι K) : ι → MvPolynomial ι K) := by
    funext i
    have hh := congrArg C (congrFun (annihilatorShear_transpose_mulVec d k hk) i)
    change C (∑ j : ι, M j i * d j) = C (d k * Pi.single k (1 : K) i) at hh
    simp only [map_sum, map_mul] at hh
    change (∑ j : ι, C (M j i) * C (d j)) =
      C (d k) * Pi.single k (1 : MvPolynomial ι K) i
    by_cases hi : i = k
    · subst i
      simpa using hh
    · simpa [Pi.single_apply, hi] using hh
  have hck : C (d k) ≠ 0 := by
    exact MvPolynomial.C_ne_zero.mpr hk
  rw [weightedLinearSubstitution_hessian]
  exact adjugate_congruence_zero_column A T b k (C (d k)) hck hT hAb ht

end Polynomial

namespace RankThreeCubic

variable {K : Type*} [Field K] [CharZero K]
private abbrev I := Unit ⊕ Fin 3
private abbrev S (K : Type*) [Field K] := MvPolynomial I K

/-- The actual maximal source layer admits a determinant-one
weight-block shear in which an entire adjugate column vanishes.
The full source determinant is unchanged by the same substitution. -/
theorem weightedLeading_exists_complementaryHessian_chart
    (w : I → ℤ) (m : ℤ) (P : S K)
    (hcap : IsWeightLE w m P)
    (hW : (Fintype.card I : ℤ) * m - 2 * (∑ i : I, w i) ≠ 0)
    {δ : K} (hdet : hessianDeterminant P = MvPolynomial.C δ) :
    ∃ (M : Matrix I I K) (k : I),
      M.det = 1 ∧
      (∀ i j, w i ≠ w j → M i j = 0) ∧
      hessianDeterminant (weightedLinearSubstitution M P) = MvPolynomial.C δ ∧
      (∀ i, (hessian (weightedLinearSubstitution M (initialForm w m P))).adjugate i k = 0) := by
  classical
  obtain ⟨s, d, hd, hs, ha⟩ := weightedLeading_exists_block_annihilator w m P hcap hW hdet
  have hex : ∃ k, d k ≠ 0 := by
    by_contra h
    push_neg at h
    exact hd (funext h)
  obtain ⟨k, hk⟩ := hex
  have hwk : w k = s := by
    by_contra h
    exact hk (hs k h)
  let M := annihilatorShear d k
  have hM : M.det = 1 := annihilatorShear_det d k
  refine ⟨M, k, hM, ?_, ?_, ?_⟩
  · apply annihilatorShear_respects_weight w d k
    intro j hj
    apply hs j
    rwa [hwk] at hj
  · rw [weightedLinearSubstitution_det M hM, hdet]
    exact (weightedLinearSubstitution M).commutes δ
  · exact weightedLinearSubstitution_zero_adjugate_column _ d k hk ha

end RankThreeCubic
end
end HC4.Polynomial
