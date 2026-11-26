import HC4.Polynomial.WeightedExtremalKernel

/-!
# Jointly affine leading planes are impossible at positive clock

If the actual maximal layer is jointly affine in two coordinates
i,j, use the signed slope

  v = m (e_i + e_j) - w.

Its sum is 2m - sum w, strictly positive at positive clock.
Every supported leading exponent u has v-weight
m (u_i + u_j - 1) <= 0. At zero-weight coordinates the slope
is nonnegative. Thus global optimality is contradicted.

In particular an identically zero 2x2 principal Hessian block is
impossible, in every determinant-one weight-compatible chart.
This excludes a family of genuinely variable kernels, not only
constant kernel directions.
-/

namespace HC4.Polynomial

open MvPolynomial HC4.Newton
open scoped BigOperators Matrix

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

private def extremalIndicator (i : Fin 4) : Fin 4 → ℤ :=
  fun k => if k = i then 1 else 0

private theorem extremalIndicator_sum (i : Fin 4) :
    (∑ k : Fin 4, extremalIndicator i k) = 1 := by
  simp [extremalIndicator]

private theorem extremalIndicator_weight (i : Fin 4) (u : Fin 4 →₀ ℕ) :
    Finsupp.weight (extremalIndicator i) u = (u i : ℤ) := by
  rw [Finsupp.weight_apply, Finsupp.sum_fintype]
  · simp [extremalIndicator]
  · intro k
    simp

/-- The support of a jointly affine plane cannot be the maximal
layer at an admissible positive-clock global optimum. -/
theorem globalWeightOptimum_no_jointlyAffine_support
    (P : MvPolynomial (Fin 4) K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ k, 0 ≤ w k) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ k, w k))
    (hopt : IsGlobalWeightOptimum P w m)
    (i j : Fin 4) :
    ∃ u ∈ (initialForm w m P).support, 1 < u i + u j := by
  classical
  let e : Fin 4 → ℤ := fun k => extremalIndicator i k + extremalIndicator j k
  let v : Fin 4 → ℤ := fun k => m * e k + (-1) * w k
  have he (k : Fin 4) : 0 ≤ e k := by
    simp only [e, extremalIndicator]
    split_ifs <;> omega
  have hvzero (k : Fin 4) (hk : w k = 0) : 0 ≤ v k := by
    simpa [v, hk] using mul_nonneg (le_of_lt hm) (he k)
  have hesum : (∑ k : Fin 4, e k) = 2 := by
    simp only [e, Finset.sum_add_distrib, extremalIndicator_sum]
    norm_num
  have hvs : (∑ k : Fin 4, v k) = 2*m - ∑ k : Fin 4, w k := by
    simp only [v, Finset.sum_add_distrib, ← Finset.mul_sum, hesum]
    ring
  have hvsum : 0 < ∑ k : Fin 4, v k := by
    rw [hvs]
    norm_num at hclock
    omega
  obtain ⟨u, hu, hpos⟩ := globalWeightOptimum_no_improvingSlope P w v m
    hw hm hcap hclock hopt hvzero hvsum
  have hwt : Finsupp.weight w u = m :=
    ((mem_support_initialForm_iff w m P u).mp hu).2
  have hew : Finsupp.weight e u = (u i : ℤ) + (u j : ℤ) := by
    have hf : e = (fun k => (1 : ℤ) * extremalIndicator i k +
        1 * extremalIndicator j k) := by
      funext k
      simp [e]
    rw [hf, firstWall_weight_scaled_add, one_mul, one_mul,
      extremalIndicator_weight, extremalIndicator_weight]
  change 0 < Finsupp.weight (fun k => m * e k + (-1) * w k) u at hpos
  rw [firstWall_weight_scaled_add, hew, hwt] at hpos
  refine ⟨u, hu, ?_⟩
  by_contra hn
  have hle : (u i : ℤ) + (u j : ℤ) ≤ 1 := by exact_mod_cast (le_of_not_gt hn)
  have hmul := mul_le_mul_of_nonneg_left hle (le_of_lt hm)
  nlinarith only [hmul, hpos]

/-- A supported monomial containing i survives differentiation
at the exponent with one i removed. -/
theorem extremal_pderiv_coeff_nonzero
    (L : MvPolynomial (Fin 4) K) (u : Fin 4 →₀ ℕ)
    (hu : coeff u L ≠ 0) (i : Fin 4) (hi : u i ≠ 0) :
    coeff (u - Finsupp.single i 1) (pderiv i L) ≠ 0 := by
  classical
  rw [coeff_pderiv_backport, Finsupp.sub_add_single_one_cancel hi]
  let a : Fin 4 →₀ ℕ := u - Finsupp.single i 1
  have hn : (a i + 1 : ℕ) ≠ 0 := by omega
  exact mul_ne_zero hu (show (((a i + 1 : ℕ) : K)) ≠ 0 by exact_mod_cast hn)

/-- A zero second derivative bounds the original monomial exponent
in the twice differentiated coordinate. -/
theorem extremal_exponent_le_one_of_second_zero
    (L : MvPolynomial (Fin 4) K) (i : Fin 4)
    (hii : hessian L i i = 0)
    (u : Fin 4 →₀ ℕ) (hu : coeff u L ≠ 0) :
    u i ≤ 1 := by
  classical
  by_contra hn
  have hi : u i ≠ 0 := by omega
  have hp := extremal_pderiv_coeff_nonzero L u hu i hi
  have hz := exponent_eq_zero_of_pderiv_eq_zero i (pderiv i L) hii _ hp
  have he := congrArg (fun a : Fin 4 →₀ ℕ => a i)
    (Finsupp.sub_add_single_one_cancel hi)
  change ((u - Finsupp.single i 1 + Finsupp.single i 1 : Fin 4 →₀ ℕ) i) = u i at he
  simp [Finsupp.add_apply, Finsupp.single_apply, hz] at he
  omega

/-- A zero mixed derivative forbids simultaneous positive
exponents in the two distinct differentiated coordinates. -/
theorem extremal_exponent_disjoint_of_mixed_zero
    (L : MvPolynomial (Fin 4) K) (i j : Fin 4) (hij : i ≠ j)
    (hij0 : hessian L i j = 0)
    (u : Fin 4 →₀ ℕ) (hu : coeff u L ≠ 0) (hi : u i ≠ 0) :
    u j = 0 := by
  classical
  have hp := extremal_pderiv_coeff_nonzero L u hu i hi
  have hz := exponent_eq_zero_of_pderiv_eq_zero j (pderiv i L) hij0 _ hp
  have he := congrArg (fun a : Fin 4 →₀ ℕ => a j)
    (Finsupp.sub_add_single_one_cancel hi)
  change ((u - Finsupp.single i 1 + Finsupp.single i 1 : Fin 4 →₀ ℕ) j) = u j at he
  simp [Finsupp.add_apply, Finsupp.single_apply, hij, Ne.symm hij, hz] at he
  omega

/-- The vanishing of the three entries of a symmetric principal
2x2 block is precisely the support obstruction needed here. -/
theorem extremal_jointlyAffine_support_of_hessian_zero
    (L : MvPolynomial (Fin 4) K) (i j : Fin 4) (hij : i ≠ j)
    (hii : hessian L i i = 0) (hjj : hessian L j j = 0)
    (hij0 : hessian L i j = 0)
    (u : Fin 4 →₀ ℕ) (hu : u ∈ L.support) :
    u i + u j ≤ 1 := by
  have hc := MvPolynomial.mem_support_iff.mp hu
  have hi := extremal_exponent_le_one_of_second_zero L i hii u hc
  have hj := extremal_exponent_le_one_of_second_zero L j hjj u hc
  by_cases he : u i = 0
  · omega
  · have hz := extremal_exponent_disjoint_of_mixed_zero L i j hij hij0 u hc he
    omega

set_option maxHeartbeats 4000000 in
/-- No jointly affine coordinate plane in any admissible
weight-preserving chart of the actual extremal source. -/
theorem globalWeightOptimum_no_zero_principalPlane
    (P : MvPolynomial (Fin 4) K) (w : Fin 4 → ℤ) (m : ℤ)
    (hw : ∀ k, 0 ≤ w k) (hm : 0 < m)
    (hcap : IsWeightLE w m P)
    (hclock : 0 < (Fintype.card (Fin 4) : ℤ)*m - 2*(∑ k, w k))
    (hopt : IsGlobalWeightOptimum P w m)
    (N : Matrix (Fin 4) (Fin 4) K) (hN : N.det = 1)
    (hblock : ∀ i j, w i ≠ w j → N i j = 0)
    (i j : Fin 4) (hij : i ≠ j) :
    let L := initialForm w m (weightedLinearSubstitution N P)
    ¬ (hessian L i i = 0 ∧ hessian L j j = 0 ∧ hessian L i j = 0) := by
  dsimp only
  rintro ⟨hii,hjj,hij0⟩
  let Q := weightedLinearSubstitution N P
  have hcapQ := weightedLinearSubstitution_isWeightLE w N hblock m P hcap
  have hoptQ := hopt.substitution N hN
  obtain ⟨u, hu, hgt⟩ := globalWeightOptimum_no_jointlyAffine_support Q w m
    hw hm hcapQ hclock hoptQ i j
  have hle := extremal_jointlyAffine_support_of_hessian_zero
    (initialForm w m Q) i j hij hii hjj hij0 u hu
  omega

end
end HC4.Polynomial

#print axioms HC4.Polynomial.globalWeightOptimum_no_jointlyAffine_support
#print axioms HC4.Polynomial.globalWeightOptimum_no_zero_principalPlane
