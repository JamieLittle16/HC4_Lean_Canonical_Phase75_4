import HC4.Polynomial.RankThreeLineRecognition
import Mathlib.Tactic

/-!
# A18.5.22: reconstruct the honest rank-three polynomial from its support

A18.5.21 extracts the univariate coefficient polynomial from an actual
multivariate polynomial supported on one finite rank-three line.  Here we
prove the inverse identity.

The proof is coefficientwise and uses only two facts:

* every supported multivariate exponent is one of the honest line exponents;
* positive `u1` makes those line exponents pairwise distinct.

Thus no convex or Laurent representation is hidden in the adapter.  An
exposed Newton edge satisfying the support predicate is literally the
`rankThreeLinePolynomial` consumed by the rank-three moment/ODE stack.
-/

namespace HC4.Polynomial

noncomputable section

/-- Range-sum presentation of a finite honest rank-three line. -/
noncomputable def rankThreeLineRangePolynomial
    {K : Type*} [CommSemiring K]
    (v2 v3 v4 u1 u2 u3 u4 M : ℕ)
    (F : MvPolynomial (Fin 4) K) : MvPolynomial (Fin 4) K :=
  ∑ j ∈ Finset.range (M + 1),
    rankThreeLineTerm v2 v3 v4 u1 u2 u3 u4 M j
      (MvPolynomial.coeff
        (rankThreeLineExponentFinsupp
          v2 v3 v4 u1 u2 u3 u4 M j) F)

/-- An actual polynomial supported on the line equals the direct finite
range-sum of its own line coefficients. -/
theorem eq_rankThreeLineRangePolynomial_of_supported
    {K : Type*} [Field K]
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hu1 : 0 < u1)
    (hsupp : IsSupportedOnRankThreeLine
      v2 v3 v4 u1 u2 u3 u4 M F) :
    F = rankThreeLineRangePolynomial
      v2 v3 v4 u1 u2 u3 u4 M F := by
  classical
  apply MvPolynomial.ext
  intro d
  by_cases hd : d ∈ F.support
  · rcases hsupp d hd with ⟨j, hj, rfl⟩
    unfold rankThreeLineRangePolynomial
    rw [MvPolynomial.coeff_sum]
    rw [Finset.sum_eq_single j]
    · rw [rankThreeLineTerm_eq_monomial]
      simp
    · intro k hk hkj
      have hExp :
          rankThreeLineExponentFinsupp
              v2 v3 v4 u1 u2 u3 u4 M k ≠
            rankThreeLineExponentFinsupp
              v2 v3 v4 u1 u2 u3 u4 M j := by
        intro heq
        have hindex :=
          rankThreeLineExponentFinsupp_injective_of_u1_pos
            v2 v3 v4 u1 u2 u3 u4 M hu1 heq
        exact hkj hindex
      rw [rankThreeLineTerm_eq_monomial]
      simp [hExp]
    · intro hjnot
      exact (hjnot (Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hj))).elim
  · have hd0 : MvPolynomial.coeff d F = 0 :=
      MvPolynomial.notMem_support_iff.mp hd
    unfold rankThreeLineRangePolynomial
    rw [MvPolynomial.coeff_sum]
    apply Eq.symm
    rw [hd0]
    apply Finset.sum_eq_zero
    intro j hj
    by_cases heq :
        rankThreeLineExponentFinsupp
            v2 v3 v4 u1 u2 u3 u4 M j = d
    · have hline0 :
          MvPolynomial.coeff
            (rankThreeLineExponentFinsupp
              v2 v3 v4 u1 u2 u3 u4 M j) F = 0 := by
        rw [heq]
        exact hd0
      rw [rankThreeLineTerm_eq_monomial]
      simp [heq, hline0]
      exact hd0
    · rw [rankThreeLineTerm_eq_monomial]
      simp [heq]

/-- A bounded univariate polynomial can be written as the complete range sum
of all of its coefficients, including the zero coefficients omitted by its
support. -/
theorem rankThreeLinePolynomial_eq_range
    {K : Type*} [Field K]
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {phi : Polynomial K}
    (hdeg : phi.natDegree ≤ M) :
    rankThreeLinePolynomial v2 v3 v4 u1 u2 u3 u4 M phi =
      ∑ j ∈ Finset.range (M + 1),
        rankThreeLineTerm v2 v3 v4 u1 u2 u3 u4 M j (phi.coeff j) := by
  classical
  unfold rankThreeLinePolynomial
  rw [Polynomial.sum_def]
  apply Finset.sum_subset
  · intro j hj
    have hjle : j ≤ M :=
      le_trans (Polynomial.le_natDegree_of_mem_supp j hj) hdeg
    exact Finset.mem_range.mpr (Nat.lt_succ_iff.mpr hjle)
  · intro j hjRange hjNot
    have hc : phi.coeff j = 0 := Polynomial.notMem_support_iff.mp hjNot
    simp [hc, rankThreeLineTerm]

/-- **Exact inverse to A18.5.4 on a genuine support line.** -/
theorem eq_rankThreeLinePolynomial_of_supported
    {K : Type*} [Field K]
    {v2 v3 v4 u1 u2 u3 u4 M : ℕ}
    {F : MvPolynomial (Fin 4) K}
    (hu1 : 0 < u1)
    (hsupp : IsSupportedOnRankThreeLine
      v2 v3 v4 u1 u2 u3 u4 M F) :
    F = rankThreeLinePolynomial
      v2 v3 v4 u1 u2 u3 u4 M
      (rankThreeLineCoefficientPolynomial
        v2 v3 v4 u1 u2 u3 u4 M F) := by
  let phi := rankThreeLineCoefficientPolynomial
    v2 v3 v4 u1 u2 u3 u4 M F
  have hdeg : phi.natDegree ≤ M := by
    dsimp [phi]
    exact rankThreeLineCoefficientPolynomial_natDegree_le
      v2 v3 v4 u1 u2 u3 u4 M F
  rw [rankThreeLinePolynomial_eq_range hdeg]
  have hrange := eq_rankThreeLineRangePolynomial_of_supported
    (F := F) hu1 hsupp
  rw [hrange]
  unfold rankThreeLineRangePolynomial
  apply Finset.sum_congr rfl
  intro j hj
  have hjle : j ≤ M := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  rw [coeff_rankThreeLineCoefficientPolynomial]
  simp [hjle, phi]

end

end HC4.Polynomial
