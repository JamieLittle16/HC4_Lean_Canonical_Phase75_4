import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneLockedOrientation
import Mathlib.Tactic

/-!
# A19 non-unit quotient orientation fixes the primitive highest slice

The preceding file synchronizes the locked ray with the non-unit quotient
parameter `V`.  The primitive highest slice must use the same orientation and
the same `V`.

The proof is only quotient-fibre bookkeeping.  Its two literal support
monomials have equal pair degree, hence the normalized carrier package puts
them in one quotient fibre.  In orientation `(1,V)` the second transverse
quotient equation reads

    V_D * n = V + V_D * (n-1),

so `V_D = V`; the swapped slice would instead give `1 = V`, impossible when
`V>1`.  The `(V,1)` case is symmetric using the first transverse quotient
coordinate.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- In quotient orientation `(1,V)`, the source-honest primitive highest slice
is the left normal form with exactly the same `V`. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_highest_slice_leftV_source_data
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    {V : ℕ}
    (hV : 1 < V)
    (Q : QsOtherFacetPrQuotientCarrierData C P 1 V)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    ∃ D : QsOtherFacetPrHighestSliceLeftSourceData C P S R,
      D.V = V := by
  rcases S.pr_highest_slice_source_data_of_nontrivial
      R hthree houtThree hnontrivial with hleft | hright
  · rcases hleft with ⟨D⟩
    have he0S : D.e0 ∈ S.slice.support := by
      rw [D.slice_support_eq]
      simp
    have he1S : D.e1 ∈ S.slice.support := by
      rw [D.slice_support_eq]
      simp
    have he0 := S.support_parent_and_pairLevel he0S
    have he1 := S.support_parent_and_pairLevel he1S
    have hq := Q.pair_fiber
      D.e0_provenance.carrier_mem D.e1_provenance.carrier_mem
      (he0.2.trans he1.2.symm)
    have hq3 := congrArg RankThreeQuotientCoordinate.secondTransverse hq
    simp only [rankThreeQuotientCoordinate_secondTransverse] at hq3
    rw [D.e0_zero, D.e1_zero, D.e0_three, D.e1_three] at hq3
    simp only [Nat.mul_zero, Nat.mul_one, zero_add] at hq3
    have hn : D.n = (D.n - 1) + 1 := by omega
    rw [hn, Nat.mul_add] at hq3
    have hDV : D.V = V := by omega
    exact ⟨D, hDV⟩
  · rcases hright with ⟨D⟩
    have he0S : D.e0 ∈ S.slice.support := by
      rw [D.slice_support_eq]
      simp
    have he1S : D.e1 ∈ S.slice.support := by
      rw [D.slice_support_eq]
      simp
    have he0 := S.support_parent_and_pairLevel he0S
    have he1 := S.support_parent_and_pairLevel he1S
    have hq := Q.pair_fiber
      D.e0_provenance.carrier_mem D.e1_provenance.carrier_mem
      (he0.2.trans he1.2.symm)
    have hq3 := congrArg RankThreeQuotientCoordinate.secondTransverse hq
    simp only [rankThreeQuotientCoordinate_secondTransverse] at hq3
    rw [D.e0_zero, D.e1_zero, D.e0_three, D.e1_three] at hq3
    simp at hq3
    omega

/-- In quotient orientation `(V,1)`, the primitive highest slice is the
transverse-swapped normal form with the same non-unit `V`. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_highest_slice_rightV_source_data
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    {V : ℕ}
    (hV : 1 < V)
    (Q : QsOtherFacetPrQuotientCarrierData C P V 1)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    ∃ D : QsOtherFacetPrHighestSliceRightSourceData C P S R,
      D.V = V := by
  rcases S.pr_highest_slice_source_data_of_nontrivial
      R hthree houtThree hnontrivial with hleft | hright
  · rcases hleft with ⟨D⟩
    have he0S : D.e0 ∈ S.slice.support := by
      rw [D.slice_support_eq]
      simp
    have he1S : D.e1 ∈ S.slice.support := by
      rw [D.slice_support_eq]
      simp
    have he0 := S.support_parent_and_pairLevel he0S
    have he1 := S.support_parent_and_pairLevel he1S
    have hq := Q.pair_fiber
      D.e0_provenance.carrier_mem D.e1_provenance.carrier_mem
      (he0.2.trans he1.2.symm)
    have hq2 := congrArg RankThreeQuotientCoordinate.firstTransverse hq
    simp only [rankThreeQuotientCoordinate_firstTransverse] at hq2
    rw [D.e0_zero, D.e1_zero, D.e0_two, D.e1_two] at hq2
    simp at hq2
    omega
  · rcases hright with ⟨D⟩
    have he0S : D.e0 ∈ S.slice.support := by
      rw [D.slice_support_eq]
      simp
    have he1S : D.e1 ∈ S.slice.support := by
      rw [D.slice_support_eq]
      simp
    have he0 := S.support_parent_and_pairLevel he0S
    have he1 := S.support_parent_and_pairLevel he1S
    have hq := Q.pair_fiber
      D.e0_provenance.carrier_mem D.e1_provenance.carrier_mem
      (he0.2.trans he1.2.symm)
    have hq2 := congrArg RankThreeQuotientCoordinate.firstTransverse hq
    simp only [rankThreeQuotientCoordinate_firstTransverse] at hq2
    rw [D.e0_zero, D.e1_zero, D.e0_two, D.e1_two] at hq2
    simp only [Nat.mul_zero, Nat.mul_one, zero_add] at hq2
    have hn : D.n = (D.n - 1) + 1 := by omega
    rw [hn, Nat.mul_add] at hq2
    have hDV : D.V = V := by omega
    exact ⟨D, hDV⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
