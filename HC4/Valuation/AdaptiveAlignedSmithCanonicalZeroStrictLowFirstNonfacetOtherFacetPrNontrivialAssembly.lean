import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrNormalizedCarrier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetContactQuadraticRees
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneContactFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseCentralActualRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseRightCentralRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseRightCrossRoofExposure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseRightCrossRoofAffineInterpolation
import Mathlib.Tactic

/-!
# A19 nontrivial PR assembly after the left finite-staircase closure

For a nontrivial highest pair slice on the `.pr` other-facet branch, the
already-verified normalized-carrier frontier has exactly three possibilities:

* the symmetric unit direction `(1,1)`;
* the left non-unit direction `(1,V)`, `V>1`; or
* the transverse-swapped right non-unit direction `(V,1)`, `V>1`.

The new finite-staircase closure completely consumes the left non-unit case.
Its exposed cross-roof alternative is contradictory, while its central
alternative lifts to an actual rank-two Hessian chart on the represented
presented state.

Thus the remaining nontrivial `.pr` assembly has only the unit branch, the
right non-unit branch, or retained actual rank-two geometry.  No repair-only
progress is asserted here.
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

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
