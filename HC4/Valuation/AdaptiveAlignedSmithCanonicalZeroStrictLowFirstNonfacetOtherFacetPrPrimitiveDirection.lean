import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrPrimitiveEndpoint
import Mathlib.Tactic

/-!
# A19 global normalization of the locked PR direction

The actual highest planar slice has now forced one of the two transverse drops
of the locked `.pr` source ray to be exactly one.  Since every fixed pair-degree
slice is parallel to that *same* locked source ray, this is not merely a local
statement about the highest slice: it normalizes the common carrier direction.

Thus, after the source-honest highest-slice argument, the locked direction is
exactly

    (1,-1,-1,-V)

or the transverse swap `(1,-1,-V,-1)`, for a positive natural `V`.  The case
`V=1` is the symmetric branch kept separate in the paper; otherwise `1<V`.
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

/-- The source ray direction is globally normalized by the primitive highest
slice.  The conclusion is stated directly in integer exponent differences, so
it applies to every later support slice without referring again to the
auxiliary affine-RR reconstruction. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_locked_direction_normal_form
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    ∃ V : ℕ, 0 < V ∧
      ((C.ray.outsideExponent 0 : ℤ) - (C.ray.facetExponent 0 : ℤ) = 1) ∧
      ((C.ray.outsideExponent 1 : ℤ) - (C.ray.facetExponent 1 : ℤ) = -1) ∧
      (((C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) = -1 ∧
          (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) =
            -(V : ℤ)) ∨
        ((C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) =
            -(V : ℤ) ∧
          (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) = -1)) := by
  rcases S.pr_endpoint_orientation_of_nontrivial
      hthree houtThree hnontrivial with ⟨D, A, horient⟩
  rcases D.direction_eq hthree houtThree with ⟨hd0, hd1, hd2, hd3⟩
  rcases horient with hleft | hright
  · rcases hleft with ⟨_hbase2, halpha, _hbase3⟩
    refine ⟨D.beta, D.beta_pos, hd0, hd1, Or.inl ?_⟩
    constructor
    · rw [hd2, halpha]
      norm_num
    · exact hd3
  · rcases hright with ⟨_hbase3, hbeta, _hbase2⟩
    refine ⟨D.alpha, D.alpha_pos, hd0, hd1, Or.inr ?_⟩
    constructor
    · exact hd2
    · rw [hd3, hbeta]
      norm_num

/-- Canonical split used by the remaining paper argument: either the locked
ray is the fully symmetric unit-drop direction, or one transverse drop is one
and the other is a genuine integer `V>1`. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_locked_direction_unit_or_V_gt_one
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    (((C.ray.outsideExponent 0 : ℤ) - (C.ray.facetExponent 0 : ℤ) = 1) ∧
      ((C.ray.outsideExponent 1 : ℤ) - (C.ray.facetExponent 1 : ℤ) = -1) ∧
      ((C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) = -1) ∧
      ((C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) = -1)) ∨
    (∃ V : ℕ, 1 < V ∧
      ((C.ray.outsideExponent 0 : ℤ) - (C.ray.facetExponent 0 : ℤ) = 1) ∧
      ((C.ray.outsideExponent 1 : ℤ) - (C.ray.facetExponent 1 : ℤ) = -1) ∧
      (((C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) = -1 ∧
          (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) =
            -(V : ℤ)) ∨
        ((C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) =
            -(V : ℤ) ∧
          (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) = -1))) := by
  rcases S.pr_locked_direction_normal_form
      hthree houtThree hnontrivial with
    ⟨V, hVpos, hd0, hd1, horient⟩
  rcases Nat.eq_one_or_one_lt_of_pos hVpos with rfl | hV
  · left
    rcases horient with h | h
    · exact ⟨hd0, hd1, h.1, by simpa using h.2⟩
    · exact ⟨hd0, hd1, by simpa using h.1, h.2⟩
  · right
    exact ⟨V, hV, hd0, hd1, horient⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
