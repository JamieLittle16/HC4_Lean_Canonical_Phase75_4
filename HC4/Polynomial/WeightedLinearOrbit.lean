import HC4.Polynomial.WeightedFixedSourceDescent

/-!
# The genuine linear orbit of a determinant-one source

Gradient collisions are transported exactly by invertible linear
substitutions. Moreover the entire linear orbit has a common finite
monomial envelope, since the all-ones weight cap is preserved.

In particular, optimization over weight presentations of arbitrary
linear charts has only finitely many possible support patterns.
This is the finite reduction, not yet the rational optimization theorem.
-/

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open scoped BigOperators Matrix

noncomputable section

variable {σ K : Type*} [Fintype σ] [DecidableEq σ] [Field K]

/-- Evaluation of the actual linear substitution. -/
theorem weightedLinearSubstitution_eval
    (M : Matrix σ σ K) (P : MvPolynomial σ K) (x : σ → K) :
    MvPolynomial.eval x (weightedLinearSubstitution M P) =
      MvPolynomial.eval (M *ᵥ x) P := by
  classical
  let f : MvPolynomial σ K →ₐ[K] K := MvPolynomial.aeval x
  have he : f.comp (weightedLinearSubstitution M) =
      MvPolynomial.aeval (M *ᵥ x) := by
    ext i
    change f (weightedLinearSubstitution M (X i)) = MvPolynomial.aeval (M *ᵥ x) (X i)
    rw [weightedLinearSubstitution, MvPolynomial.aeval_X, MvPolynomial.aeval_X]
    change MvPolynomial.eval x (∑ j : σ, MvPolynomial.C (M i j) * X j) = (M *ᵥ x) i
    simp [Matrix.mulVec, dotProduct]
  exact AlgHom.congr_fun he P

/-- Gradient covariance on the whole source, not only on its maximal layer. -/
theorem weightedLinearSubstitution_gradient
    (M : Matrix σ σ K) (P : MvPolynomial σ K) (x : σ → K) :
    (fun j : σ => MvPolynomial.eval x (pderiv j (weightedLinearSubstitution M P))) =
      M.transpose *ᵥ (fun j : σ => MvPolynomial.eval (M *ᵥ x) (pderiv j P)) := by
  classical
  funext j
  rw [weightedLinearSubstitution_partial, map_sum]
  change (∑ i : σ, MvPolynomial.eval x
    (weightedLinearSubstitution M (pderiv i P) * MvPolynomial.C (M i j))) =
      ∑ i : σ, M i j * MvPolynomial.eval (M *ᵥ x) (pderiv i P)
  apply Finset.sum_congr rfl
  intro i _
  rw [map_mul, MvPolynomial.eval_C, weightedLinearSubstitution_eval, mul_comm]

/-- Linear chart changes preserve and reflect gradient injectivity. -/
theorem weightedLinearSubstitution_gradient_injective_iff
    (M : Matrix σ σ K) (hM : M.det = 1) (P : MvPolynomial σ K) :
    Function.Injective (fun x : σ → K => fun j : σ =>
      MvPolynomial.eval x (pderiv j (weightedLinearSubstitution M P))) ↔
    Function.Injective (fun x : σ → K => fun j : σ =>
      MvPolynomial.eval x (pderiv j P)) := by
  classical
  have hu : IsUnit M := (Matrix.isUnit_iff_isUnit_det M).mpr (by rw [hM]; exact isUnit_one)
  have hut : IsUnit M.transpose := (Matrix.isUnit_iff_isUnit_det M.transpose).mpr
    (by rw [Matrix.det_transpose, hM]; exact isUnit_one)
  have hi : Function.Injective M.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hu
  have hs : Function.Surjective M.mulVec := Matrix.mulVec_surjective_iff_isUnit.mpr hu
  have hit : Function.Injective M.transpose.mulVec := Matrix.mulVec_injective_iff_isUnit.mpr hut
  constructor
  · intro h x y hxy
    obtain ⟨u, hu'⟩ := hs x
    obtain ⟨v, hv'⟩ := hs y
    have he : (fun j : σ => MvPolynomial.eval u (pderiv j (weightedLinearSubstitution M P))) =
        (fun j : σ => MvPolynomial.eval v (pderiv j (weightedLinearSubstitution M P))) := by
      rw [weightedLinearSubstitution_gradient, weightedLinearSubstitution_gradient, hu', hv', hxy]
    rw [← hu', ← hv', h he]
  · intro h x y hxy
    rw [weightedLinearSubstitution_gradient, weightedLinearSubstitution_gradient] at hxy
    exact hi (h (hit hxy))

/-- Composition stays in the genuine linear orbit. -/
theorem weightedLinearSubstitution_comp
    (M N : Matrix σ σ K) (P : MvPolynomial σ K) :
    weightedLinearSubstitution N (weightedLinearSubstitution M P) =
      weightedLinearSubstitution (M * N) P := by
  classical
  have he : (weightedLinearSubstitution N).comp (weightedLinearSubstitution M) =
      weightedLinearSubstitution (M * N) := by
    ext i
    change weightedLinearSubstitution N (weightedLinearSubstitution M (X i)) =
      weightedLinearSubstitution (M * N) (X i)
    simp only [weightedLinearSubstitution, MvPolynomial.aeval_X, map_sum, map_mul,
      MvPolynomial.aeval_C, MvPolynomial.algebraMap_eq, Matrix.mul_apply, map_sum]
    simp only [Finset.mul_sum, Finset.sum_mul, map_mul, mul_assoc]
    exact Finset.sum_comm
  exact AlgHom.congr_fun he P

/-- The all-ones weight is exactly ordinary monomial degree. -/
theorem weight_allOnes_eq_degree (u : σ →₀ ℕ) :
    Finsupp.weight (fun _ : σ => (1 : ℤ)) u = ((u.sum fun _ n => n : ℕ) : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum, Finsupp.sum]
  simp [nsmul_eq_mul]

/-- All linear substitutions preserve a total-degree upper bound. -/
theorem weightedLinearSubstitution_totalDegree_le
    (M : Matrix σ σ K) (P : MvPolynomial σ K) :
    (weightedLinearSubstitution M P).totalDegree ≤ P.totalDegree := by
  classical
  let w : σ → ℤ := fun _ => 1
  have hcap : IsWeightLE w (P.totalDegree : ℤ) P := by
    intro u hu
    rw [show w = (fun _ : σ => (1 : ℤ)) from rfl, weight_allOnes_eq_degree]
    exact_mod_cast MvPolynomial.le_totalDegree hu
  have hcap' := weightedLinearSubstitution_isWeightLE w M (by simp [w])
    (P.totalDegree : ℤ) P hcap
  change ((weightedLinearSubstitution M P).support.sup (fun u => u.sum fun _ n => n)) ≤ P.totalDegree
  apply Finset.sup_le
  intro u hu
  have he := hcap' hu
  change Finsupp.weight (fun _ : σ => (1 : ℤ)) u ≤ (P.totalDegree : ℤ) at he
  rw [weight_allOnes_eq_degree] at he
  exact_mod_cast he

/-- A common finite envelope for every exponent of bounded total degree. -/
def degreeExponentEnvelope (σ : Type*) [Fintype σ] (D : ℕ) : Finset (σ →₀ ℕ) := by
  classical
  exact Finset.univ.image (fun a : σ → Fin (D+1) =>
    Finsupp.equivFunOnFinite.symm (fun i => (a i : ℕ)))

theorem support_subset_degreeExponentEnvelope
    (P : MvPolynomial σ K) (D : ℕ) (hD : P.totalDegree ≤ D) :
    P.support ⊆ degreeExponentEnvelope σ D := by
  classical
  intro u hu
  have hsum := (MvPolynomial.le_totalDegree hu).trans hD
  have hcoord (i : σ) : u i ≤ D := by
    by_cases hi : i ∈ u.support
    · have he : u i ≤ u.sum (fun _ n => n) := by
        unfold Finsupp.sum
        exact Finset.single_le_sum (fun j _ => Nat.zero_le (u j)) hi
      exact he.trans hsum
    · have hz : u i = 0 := by
        by_contra hn
        exact hi (Finsupp.mem_support_iff.mpr hn)
      simp [hz]
  unfold degreeExponentEnvelope
  apply Finset.mem_image.mpr
  refine ⟨fun i => ⟨u i, Nat.lt_succ_of_le (hcoord i)⟩, Finset.mem_univ _, ?_⟩
  exact Finsupp.equivFunOnFinite.symm_apply_apply u

/-- Only finitely many support patterns can occur in the entire
linear orbit. The bound is independent of the entries of the chart. -/
theorem weightedLinearOrbit_support_mem
    (P : MvPolynomial σ K) (M : Matrix σ σ K) :
    (weightedLinearSubstitution M P).support ∈
      (degreeExponentEnvelope σ P.totalDegree).powerset := by
  classical
  exact Finset.mem_powerset.mpr
    (support_subset_degreeExponentEnvelope _ _ (weightedLinearSubstitution_totalDegree_le M P))

/-- A finite set of actual realized determinant-one support patterns.
Every member has a genuine chart witness, and every chart occurs. -/
theorem exists_finite_linearOrbit_support_patterns
    (P : MvPolynomial σ K) :
    ∃ S : Finset (Finset (σ →₀ ℕ)), ∀ T : Finset (σ →₀ ℕ),
      T ∈ S ↔ ∃ M : Matrix σ σ K, M.det = 1 ∧
        (weightedLinearSubstitution M P).support = T := by
  classical
  refine ⟨(degreeExponentEnvelope σ P.totalDegree).powerset.filter
    (fun T => ∃ M : Matrix σ σ K, M.det = 1 ∧
      (weightedLinearSubstitution M P).support = T), ?_⟩
  intro T
  constructor
  · intro h
    exact (Finset.mem_filter.mp h).2
  · rintro ⟨M, hM, rfl⟩
    exact Finset.mem_filter.mpr ⟨weightedLinearOrbit_support_mem P M, M, hM, rfl⟩

end
end HC4.Polynomial

#print axioms HC4.Polynomial.weightedLinearSubstitution_gradient_injective_iff
#print axioms HC4.Polynomial.exists_finite_linearOrbit_support_patterns
