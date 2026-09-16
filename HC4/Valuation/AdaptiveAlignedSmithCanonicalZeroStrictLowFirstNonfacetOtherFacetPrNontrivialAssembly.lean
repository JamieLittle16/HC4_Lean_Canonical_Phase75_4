import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrNormalizedCarrier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitEndpointOrientation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitEndpointNormalization
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitContactFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitQuotientInterpolation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitStaircaseSupport
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitContactSeparation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitStaircaseClassification
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitPairRees
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitEndpointClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneTwoFunctionReconstruction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactQuadraticRees
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneContactFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCentralActualRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseRightCentralActualRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseRightCrossRoofAffineTerminalRealisation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseRightClosure
import Mathlib.Tactic

/-!
# A19 nontrivial PR assembly after the finite-staircase closures

For a nontrivial highest pair slice on the `.pr` other-facet branch, the
already-verified normalized-carrier frontier has exactly three possibilities:

* the symmetric unit direction `(1,1)`;
* the left non-unit direction `(1,V)`, `V>1`; or
* the transverse-swapped right non-unit direction `(V,1)`, `V>1`.

The finite-staircase closure consumes both non-unit directions.  In each case,
the exposed cross-roof alternative is contradictory, while the central
alternative lifts to an actual rank-two Hessian chart on the represented
presented state.

Thus the remaining nontrivial `.pr` assembly has only the unit branch or
retained actual rank-two geometry.  No repair-only progress is asserted here.
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

/-- **Consume the left `(1,V)`, `V>1` branch of the normalized `.pr`
frontier.**  The same honest contact-Rees package is retained for the two
remaining quotient orientations. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_nontrivial_after_left_closure
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    ∃ R : QsOtherFacetContactQuadraticReesPackage C,
      Nonempty (QsOtherFacetPrQuotientCarrierData C P 1 1) ∨
        Nonempty (QsOtherFacetPrRightVContactFrontierData C P S R) ∨
        Nonempty
          (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
            T.terminal.blocker.presented) := by
  rcases C.qs_ray_otherFacet_contactQuadraticRees_package
      hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree with ⟨R⟩
  refine ⟨R, ?_⟩
  rcases S.pr_normalizedCarrier_frontier hthree houtThree hnontrivial with
    hunit | hnonunit
  · exact Or.inl hunit
  · rcases hnonunit with ⟨V, hV, hleft | hright⟩
    · rcases hleft with ⟨Q⟩
      rcases S.pr_leftV_contactFrontier
          R hV Q hthree houtThree hnontrivial with ⟨F⟩
      rcases F.centralRankTwoGeometry hthree houtThree with ⟨G⟩
      exact Or.inr (Or.inr ⟨G.actualRankTwoHessianChart⟩)
    · rcases hright with ⟨Q⟩
      exact Or.inr (Or.inl <|
        S.pr_rightV_contactFrontier
          R hV Q hthree houtThree hnontrivial)

/-- **Consume both non-unit finite-staircase directions.**  After the left and
right closures, a nontrivial `.pr` highest slice is either the symmetric unit
quotient `(1,1)` or it already carries an actual rank-two Hessian chart on the
represented state. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_nontrivial_after_nonunit_closure
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    ∃ R : QsOtherFacetContactQuadraticReesPackage C,
      Nonempty (QsOtherFacetPrQuotientCarrierData C P 1 1) ∨
        Nonempty
          (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
            T.terminal.blocker.presented) := by
  rcases S.pr_nontrivial_after_left_closure
      hthree houtThree hnontrivial with ⟨R, hunit | hrest⟩
  · exact ⟨R, Or.inl hunit⟩
  · rcases hrest with hright | hrank
    · rcases hright with ⟨F⟩
      exact ⟨R, Or.inr (F.actualRankTwoHessianChart hthree houtThree)⟩
    · exact ⟨R, Or.inr hrank⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation