module

public import HC4.Polynomial.WeightedComplementaryHessian

/-!
# Exact weighted initial forms in the complementary chart

A linear substitution with no cross-weight entries maps each monomial
into its original exact weighted component. It therefore commutes
with every initial-form projection and preserves every upper bound.

Apply this to the determinant-one annihilator shear. The vanishing
complementary principal Hessian determinant is now a statement about
the actual leading layer of the transformed full source.
-/

public section

namespace HC4.Polynomial

open MvPolynomial
open scoped Matrix BigOperators

noncomputable section

variable {ι K : Type*} [Fintype ι] [DecidableEq ι] [Field K]

theorem weightedLinearSubstitution_X_homogeneous
    (w : ι → ℤ) (M : Matrix ι ι K)
    (hM : ∀ i j, w i ≠ w j → M i j = 0) (i : ι) :
    MvPolynomial.IsWeightedHomogeneous w (weightedLinearSubstitution M (X i)) (w i) := by
  classical
  rw [weightedLinearSubstitution, MvPolynomial.aeval_X]
  apply MvPolynomial.IsWeightedHomogeneous.sum Finset.univ
    (fun j : ι => MvPolynomial.C (M i j) * X j) (w i)
  intro j _
  by_cases h : w i = w j
  · rw [h]
    simpa only [zero_add] using
      (MvPolynomial.isWeightedHomogeneous_C w (M i j)).mul
        (MvPolynomial.isWeightedHomogeneous_X K w j)
  · rw [hM i j h, map_zero, zero_mul]
    exact MvPolynomial.isWeightedHomogeneous_zero K w _

theorem weightedLinearSubstitution_monomial_homogeneous
    (w : ι → ℤ) (M : Matrix ι ι K)
    (hM : ∀ i j, w i ≠ w j → M i j = 0)
    (u : ι →₀ ℕ) (a : K) :
    MvPolynomial.IsWeightedHomogeneous w
      (weightedLinearSubstitution M (monomial u a)) (Finsupp.weight w u) := by
  classical
  unfold weightedLinearSubstitution
  rw [MvPolynomial.aeval_monomial]
  have hp : MvPolynomial.IsWeightedHomogeneous w
      (∏ i ∈ u.support, (∑ j : ι, MvPolynomial.C (M i j) * X j) ^ u i)
      (∑ i ∈ u.support, u i • w i) := by
    apply MvPolynomial.IsWeightedHomogeneous.prod u.support
      (fun i => (∑ j : ι, MvPolynomial.C (M i j) * X j) ^ u i)
      (fun i => u i • w i)
    intro i _
    have hi := weightedLinearSubstitution_X_homogeneous w M hM i
    change MvPolynomial.IsWeightedHomogeneous w
      (MvPolynomial.aeval (fun i => ∑ j : ι, MvPolynomial.C (M i j) * X j) (X i))
      (w i) at hi
    rw [MvPolynomial.aeval_X] at hi
    exact hi.pow (u i)
  have hh := (MvPolynomial.isWeightedHomogeneous_C w a).mul hp
  simpa only [zero_add, MvPolynomial.algebraMap_eq, Finsupp.prod, Finsupp.weight,
    LinearMap.toAddMonoidHom_coe, Finsupp.linearCombination_apply, Finsupp.sum] using hh

/-- Exact weight projection commutes with the genuine linear
substitution, not just with its leading approximation. -/
theorem weightedLinearSubstitution_initialForm
    (w : ι → ℤ) (M : Matrix ι ι K)
    (hM : ∀ i j, w i ≠ w j → M i j = 0)
    (m : ℤ) (P : MvPolynomial ι K) :
    initialForm w m (weightedLinearSubstitution M P) =
      weightedLinearSubstitution M (initialForm w m P) := by
  classical
  refine MvPolynomial.induction_on' P ?_ ?_
  · intro u a
    have hp := weightedLinearSubstitution_monomial_homogeneous w M hM u a
    have hmono : MvPolynomial.IsWeightedHomogeneous w
        (monomial u a : MvPolynomial ι K) (Finsupp.weight w u) :=
      MvPolynomial.isWeightedHomogeneous_monomial w u a rfl
    by_cases h : m = Finsupp.weight w u
    · rw [h, initialForm_eq_self_of_isWeightedHomogeneous hp,
        initialForm_eq_self_of_isWeightedHomogeneous hmono]
    · rw [initialForm_eq_zero_of_isWeightedHomogeneous hp m h,
        initialForm_eq_zero_of_isWeightedHomogeneous hmono m h, map_zero]
  · intro p q hp hq
    simp only [map_add, hp, hq]

/-- In particular no higher-weight term is introduced. -/
theorem weightedLinearSubstitution_isWeightLE
    (w : ι → ℤ) (M : Matrix ι ι K)
    (hM : ∀ i j, w i ≠ w j → M i j = 0)
    (m : ℤ) (P : MvPolynomial ι K) (hcap : IsWeightLE w m P) :
    IsWeightLE w m (weightedLinearSubstitution M P) := by
  classical
  intro u hu
  by_contra h
  have hgt : m < Finsupp.weight w u := lt_of_not_ge h
  have hz : initialForm w (Finsupp.weight w u) (weightedLinearSubstitution M P) = 0 := by
    rw [weightedLinearSubstitution_initialForm w M hM,
      initialForm_eq_zero_of_isWeightLE hcap hgt, map_zero]
  have he := congrArg (coeff u) hz
  rw [coeff_initialForm, if_pos rfl] at he
  exact (MvPolynomial.mem_support_iff.mp hu) he

namespace RankThreeCubic

variable {F : Type*} [Field F] [CharZero F]
namespace WeightedComplementaryInitialForm

abbrev I := Unit ⊕ Fin 3
abbrev S (F : Type*) [Field F] := MvPolynomial I F

end WeightedComplementaryInitialForm

open WeightedComplementaryInitialForm (I S)

/-- The complementary principal minor at any coordinate is the
longitudinal principal minor in a permuted matrix. -/
theorem complementary_principalDet_eq_adjugate
    {R : Type*} [CommRing R] (A : Matrix I I R) (k : I) :
    (A.submatrix
      (fun i : Fin 3 => Equiv.swap (.inl ()) k (.inr i))
      (fun i : Fin 3 => Equiv.swap (.inl ()) k (.inr i))).det =
      A.adjugate k k := by
  classical
  let e : I ≃ I := Equiv.swap (.inl ()) k
  have he := longitudinal_principalCofactor_eq_transverseDet (A.submatrix e e)
  rw [Matrix.adjugate_submatrix_equiv_self] at he
  have hk : e (.inl ()) = k := by simp [e]
  change A.adjugate (e (.inl ())) (e (.inl ())) = _ at he
  rw [hk] at he
  exact he.symm

/-- A determinant-one weight-preserving chart on the full source,
with a singular complementary Hessian in its actual maximal layer.
The zero adjugate column is retained as stronger information. -/
theorem weightedLeading_exists_actual_complementaryHessian
    (w : I → ℤ) (m : ℤ) (P : S F)
    (hcap : IsWeightLE w m P)
    (hW : (Fintype.card I : ℤ) * m - 2 * (∑ i : I, w i) ≠ 0)
    {δ : F} (hdet : hessianDeterminant P = MvPolynomial.C δ) :
    ∃ (M : Matrix I I F) (k : I),
      M.det = 1 ∧
      (∀ i j, w i ≠ w j → M i j = 0) ∧
      let P' := weightedLinearSubstitution M P
      let L' := initialForm w m P'
      IsWeightLE w m P' ∧
      hessianDeterminant P' = MvPolynomial.C δ ∧
      (∀ i, (hessian L').adjugate i k = 0) ∧
      ((hessian L').submatrix
        (fun i : Fin 3 => Equiv.swap (.inl ()) k (.inr i))
        (fun i : Fin 3 => Equiv.swap (.inl ()) k (.inr i))).det = 0 := by
  classical
  obtain ⟨M, k, hM, hw, hdet', hcol⟩ :=
    weightedLeading_exists_complementaryHessian_chart w m P hcap hW hdet
  refine ⟨M, k, hM, hw, weightedLinearSubstitution_isWeightLE w M hw m P hcap,
    hdet', ?_, ?_⟩
  · rw [weightedLinearSubstitution_initialForm w M hw]
    exact hcol
  · rw [complementary_principalDet_eq_adjugate,
      weightedLinearSubstitution_initialForm w M hw]
    exact hcol k

end RankThreeCubic
end
end HC4.Polynomial

#print axioms HC4.Polynomial.RankThreeCubic.weightedLeading_exists_actual_complementaryHessian
