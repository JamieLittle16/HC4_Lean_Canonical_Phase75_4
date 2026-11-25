import HC4.Polynomial.RationalCharacteristicRankOneAffineFrontier

/-!
# Affine coordinates for the rational characteristic obstruction

Complete two independent constant covectors to a three-dimensional
coordinate frame. Prove the arbitrary-degree polynomial Hessian
chain rule for an affine substitution. Unlike the earlier cubic
tensor congruence, this acts on the actual reference polynomial.

Fraction-field substitution and transport of the rank-one operator
are separate from this polynomial chain rule.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {K : Type*} [Field K]

private abbrev B (K : Type*) [Field K] := MvPolynomial (Fin 3) K

/-- Two independent covectors can be completed by a coordinate
covector. An explicit minor argument avoids choosing abstract bases. -/
theorem rationalAffine_complete_covectors
    (A D : Fin 3 → K)
    (hind : ∀ a b : K, (∀ j : Fin 3, a * A j + b * D j = 0) →
      a = 0 ∧ b = 0) :
    ∃ M : Matrix (Fin 3) (Fin 3) K,
      M.det ≠ 0 ∧ (∀ j, M 0 j = A j) ∧ (∀ j, M 1 j = D j) := by
  classical
  have hex : ∃ k : Fin 3, A k ≠ 0 := by
    by_contra h
    have hz (j : Fin 3) : A j = 0 := by
      by_contra hj
      exact h ⟨j, hj⟩
    have hh := hind 1 0 (by intro j; simp [hz j])
    exact one_ne_zero hh.1
  obtain ⟨k, hk⟩ := hex
  have hm : ∃ i j : Fin 3, A i * D j - A j * D i ≠ 0 := by
    by_contra h
    have hz (j : Fin 3) : A k * D j - A j * D k = 0 := by
      by_contra hj
      exact h ⟨k, j, hj⟩
    have hh := hind (-D k) (A k) (by
      intro j
      linear_combination hz j)
    exact hk hh.2
  obtain ⟨i, j, hij⟩ := hm
  have hor : A 0 * D 1 - A 1 * D 0 ≠ 0 ∨
      A 0 * D 2 - A 2 * D 0 ≠ 0 ∨
      A 1 * D 2 - A 2 * D 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hij
    obtain ⟨h01, h02, h12⟩ := h
    fin_cases i <;> fin_cases j
    · ring
    · exact h01
    · exact h02
    · change A 1 * D 0 - A 0 * D 1 = 0
      linear_combination -h01
    · ring
    · exact h12
    · change A 2 * D 0 - A 0 * D 2 = 0
      linear_combination -h02
    · change A 2 * D 1 - A 1 * D 2 = 0
      linear_combination -h12
    · ring
  rcases hor with h01 | h02 | h12
  · refine ⟨![A, D, ![0, 0, 1]], ?_, ?_, ?_⟩
    · have he : Matrix.det (![A, D, ![0, 0, 1]] : Matrix (Fin 3) (Fin 3) K) =
          A 0 * D 1 - A 1 * D 0 := by
        simp [Matrix.det_fin_three] <;> ring
      rw [he]
      exact h01
    · intro j
      rfl
    · intro j
      rfl
  · refine ⟨![A, D, ![0, 1, 0]], ?_, ?_, ?_⟩
    · have he : Matrix.det (![A, D, ![0, 1, 0]] : Matrix (Fin 3) (Fin 3) K) =
          -(A 0 * D 2 - A 2 * D 0) := by
        simp [Matrix.det_fin_three] <;> ring
      rw [he]
      exact neg_ne_zero.mpr h02
    · intro j
      rfl
    · intro j
      rfl
  · refine ⟨![A, D, ![1, 0, 0]], ?_, ?_, ?_⟩
    · have he : Matrix.det (![A, D, ![1, 0, 0]] : Matrix (Fin 3) (Fin 3) K) =
          A 1 * D 2 - A 2 * D 1 := by
        simp [Matrix.det_fin_three] <;> ring
      rw [he]
      exact h12
    · intro j
      rfl
    · intro j
      rfl

/-- The substitution x = M y + c on the actual polynomial ring. -/
def rationalAffine_substitution
    (M : Matrix (Fin 3) (Fin 3) K) (c : Fin 3 → K) : B K →ₐ[K] B K :=
  MvPolynomial.aeval (fun i =>
    MvPolynomial.C (c i) + ∑ j : Fin 3, MvPolynomial.C (M i j) * X j)

/-- The partials of the affine coordinates are exactly the entries
of their constant coordinate matrix. -/
theorem rationalAffine_substitution_X_partial
    (M : Matrix (Fin 3) (Fin 3) K) (c : Fin 3 → K)
    (i j : Fin 3) :
    pderiv j (rationalAffine_substitution M c (X i)) =
      MvPolynomial.C (M i j) := by
  classical
  unfold rationalAffine_substitution
  rw [MvPolynomial.aeval_X, map_add, pderiv_C, zero_add, map_sum]
  simp only [MvPolynomial.pderiv_C_mul]
  rw [Finset.sum_eq_single j]
  · simp
  · intro k _ hk
    rw [pderiv_X_of_ne hk, mul_zero]
  · simp

/-- The actual first derivative chain rule, with no restriction on
the degree or homogeneous components of the source. -/
theorem rationalAffine_substitution_partial
    (M : Matrix (Fin 3) (Fin 3) K) (c : Fin 3 → K)
    (f : B K) (j : Fin 3) :
    pderiv j (rationalAffine_substitution M c f) =
      ∑ i : Fin 3, rationalAffine_substitution M c (pderiv i f) *
        MvPolynomial.C (M i j) := by
  let w : Fin 3 → B K := fun i =>
    MvPolynomial.C (c i) + ∑ k : Fin 3, MvPolynomial.C (M i k) * X k
  change pderiv j (MvPolynomial.aeval w f) =
    ∑ i : Fin 3, MvPolynomial.aeval w (pderiv i f) *
      MvPolynomial.C (M i j)
  rw [derivation_aeval]
  apply Finset.sum_congr rfl
  intro i _
  have h := rationalAffine_substitution_X_partial M c i j
  change pderiv j (MvPolynomial.aeval w (X i)) = MvPolynomial.C (M i j) at h
  rw [MvPolynomial.aeval_X] at h
  rw [h]

/-- The polynomial Hessian transforms by the genuine congruence
formula under affine substitution. This is a source identity,
not an evaluation-only or cubic-tensor surrogate. -/
theorem rationalAffine_substitution_hessian
    (M : Matrix (Fin 3) (Fin 3) K) (c : Fin 3 → K) (f : B K) :
    hessian (rationalAffine_substitution M c f) =
      (M.map (MvPolynomial.C : K →+* B K)).transpose *
        (hessian f).map (rationalAffine_substitution M c).toRingHom *
        M.map (MvPolynomial.C : K →+* B K) := by
  classical
  apply Matrix.ext
  intro i j
  simp only [hessian_apply]
  rw [rationalAffine_substitution_partial M c f i, map_sum]
  simp only [Derivation.leibniz, smul_eq_mul, pderiv_C, mul_zero, zero_add]
  simp only [rationalAffine_substitution_partial, Matrix.mul_apply,
    Matrix.transpose_apply, Matrix.map_apply, hessian_apply]
  change (∑ a : Fin 3, MvPolynomial.C (M a i) *
      (∑ b : Fin 3, rationalAffine_substitution M c (pderiv b (pderiv a f)) *
        MvPolynomial.C (M b j))) =
    ∑ b : Fin 3, (∑ a : Fin 3, MvPolynomial.C (M a i) *
      rationalAffine_substitution M c (pderiv b (pderiv a f))) *
        MvPolynomial.C (M b j)
  simp only [Fin.sum_univ_three]
  ring

end
end HC4.Polynomial.RankThreeCubic
