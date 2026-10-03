import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralDeficitZeroSchur
import HC4.Newton.SingularSchurDiagonalGap
import Mathlib.Tactic

/-!
# The first central Schur order is exactly the first source-deficit order

The source-honest first total-deficit layer occurs at
`G.firstDeficitOrder`.  Both principal cleared Schur entries are the two
first-deficit roof determinants, so their positive coefficients vanish below
that order.  Since the complete Schur determinant is identically zero, the
generic diagonal-gap lemma forces the off-diagonal Schur entry to have the
same lower gap.

At the first-deficit order, the singleton-axis source theorem and the exact
rank-three-roof coefficient calculation give a nonzero coefficient in one of
the two principal Schur entries.  Therefore the abstract zero-Schur selector
chooses exactly the honest source order.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
namespace QsOtherFacetPrLeftVCentralRankTwoGeometry

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (G : QsOtherFacetPrLeftVCentralRankTwoGeometry F)

/-- **Exact first Schur order.** -/
theorem centralDeficitZeroSchur_firstPositiveEntryOrder_eq_firstDeficitOrder
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    let Z := G.centralDeficitZeroSchurSeries hthree houtThree
    let hz := G.centralDeficitZeroSchurSeries_hasPositiveEntryLayer
      hthree houtThree
    Z.firstPositiveEntryOrder hz = G.firstDeficitOrder := by
  let Z := G.centralDeficitZeroSchurSeries hthree houtThree
  let hz := G.centralDeficitZeroSchurSeries_hasPositiveEntryLayer
    hthree houtThree
  let q := G.firstDeficitOrder

  have hactiveGap :
      ∀ n : ℕ, n < q → Z.series.active.coeff n = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      exact Z.active_coeff_zero
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      change G.centralDeficitSchurBlock.schurA.coeff n = 0
      rw [G.centralDeficitSchurA_eq_rightRoofDet]
      exact G.firstDeficitRightActiveHessian_det_gap n hnpos hn

  have hkernelGap :
      ∀ n : ℕ, n < q → Z.series.kernel.coeff n = 0 := by
    intro n hn
    by_cases hn0 : n = 0
    · subst n
      exact Z.kernel_coeff_zero
    · have hnpos : 0 < n := Nat.pos_of_ne_zero hn0
      change G.centralDeficitSchurBlock.schurC.coeff n = 0
      rw [G.centralDeficitSchurC_eq_leftRoofDet]
      exact G.firstDeficitLeftActiveHessian_det_gap n hnpos hn

  have hdetZ : Z.series.determinant = 0 := by
    change G.centralDeficitSchurBlock.polynomialSchurSeries.determinant = 0
    exact G.centralDeficitSchurSeries_determinant_eq_zero

  have hoffGap :
      ∀ n : ℕ, n < q → Z.series.offDiag.coeff n = 0 :=
    Z.series.offDiag_coeff_eq_zero_below_of_diagonal_gap
      q hactiveGap hkernelGap hdetZ

  have hentry :
      Z.series.active.coeff q ≠ 0 ∨
        Z.series.kernel.coeff q ≠ 0 := by
    rcases G.firstDeficitLayer_singleton_axis hthree houtThree with
      hleft | hright
    · rcases hleft with ⟨e, he, he1, he2, huniq⟩
      right
      change G.centralDeficitSchurBlock.schurC.coeff q ≠ 0
      rw [G.centralDeficitSchurC_eq_leftRoofDet]
      simpa [q] using
        G.firstDeficitLeftActiveHessian_det_coeff_first_ne_zero
          hthree houtThree he he1 he2 huniq
    · rcases hright with ⟨e, he, he1, he2, huniq⟩
      left
      change G.centralDeficitSchurBlock.schurA.coeff q ≠ 0
      rw [G.centralDeficitSchurA_eq_rightRoofDet]
      simpa [q] using
        G.firstDeficitRightActiveHessian_det_coeff_first_ne_zero
          hthree houtThree he he1 he2 huniq

  have hqpos : 0 < q := by
    exact G.firstDeficitOrder_pos

  have hqmem : q ∈ Z.positiveEntryOrders := by
    apply Finset.mem_filter.mpr
    constructor
    · apply Finset.mem_union.mpr
      rcases hentry with hA | hC
      · left
        exact Polynomial.mem_support_iff.mpr hA
      · right
        apply Finset.mem_union.mpr
        right
        exact Polynomial.mem_support_iff.mpr hC
    · exact hqpos

  have hfirstLe :
      Z.firstPositiveEntryOrder hz ≤ q := by
    unfold ZeroSchurSeries.firstPositiveEntryOrder
    exact Finset.min'_le Z.positiveEntryOrders q hqmem

  have hfirstGe :
      q ≤ Z.firstPositiveEntryOrder hz := by
    by_contra hnot
    have hlt :
        Z.firstPositiveEntryOrder hz < q := by omega
    have hm := Z.firstPositiveEntryOrder_mem hz
    have hu := (Finset.mem_filter.mp hm).1
    rcases Finset.mem_union.mp hu with hA | hrest
    · have hne :=
        Polynomial.mem_support_iff.mp hA
      exact hne (hactiveGap _ hlt)
    · rcases Finset.mem_union.mp hrest with hB | hC
      · have hne :=
          Polynomial.mem_support_iff.mp hB
        exact hne (hoffGap _ hlt)
      · have hne :=
          Polynomial.mem_support_iff.mp hC
        exact hne (hkernelGap _ hlt)

  exact Nat.le_antisymm hfirstLe hfirstGe

end QsOtherFacetPrLeftVCentralRankTwoGeometry
end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
