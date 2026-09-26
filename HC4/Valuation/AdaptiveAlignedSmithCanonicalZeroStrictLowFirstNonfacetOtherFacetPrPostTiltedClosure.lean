import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrNontrivialAssembly
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneCentralDeficitTiltedClosure
import Mathlib.Tactic

/-!
# Post-Commit-C `.pr` assembly

The old nontrivial `.pr` collector predates the tilted central-deficit
contradiction.  Its left non-unit branch therefore retained an actual rank-two
chart even after the finite-staircase central geometry had been isolated.

Commit C proves that this central survivor is itself impossible.  This file
threads that stronger theorem through the first old assembly seam and reruns
only the normalized `.pr` split:

* left `(1,V)`, `V > 1`: contradiction;
* right `(V,1)`, `V > 1`: retain the existing actual rank-two chart;
* unit `(1,1)`: retain the existing source-honest unit closures.

No tilted argument is mirrored to the right or unit orientations.
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

/-- **Post-C left non-unit contradiction.**

The old central-roof closure already removes the exposed cross-roof branch and
packages its only survivor as `QsOtherFacetPrLeftVCentralRankTwoGeometry`.
The tilted closure proves that survivor impossible. -/
theorem QsOtherFacetPrLeftVContactFrontierData.impossible_after_tiltedClosure
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    False := by
  rcases F.centralRankTwoGeometry hthree houtThree with ⟨G⟩
  exact G.centralDeficit_impossible hthree houtThree

/-- **Post-C normalized nontrivial `.pr` collector.**

The left non-unit constructor has disappeared.  The only normalized survivors
are the unit quotient and the right non-unit contact frontier. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_nontrivial_after_tiltedClosure
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
        Nonempty (QsOtherFacetPrRightVContactFrontierData C P S R) := by
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
      exact (F.impossible_after_tiltedClosure hthree houtThree).elim
    · rcases hright with ⟨Q⟩
      exact Or.inr
        (S.pr_rightV_contactFrontier
          R hV Q hthree houtThree hnontrivial)

/-- Assembly-facing post-C form.  Every surviving normalized nontrivial
`.pr` branch still carries the already-verified represented-state rank-two
Hessian chart, but the left non-unit route now reaches this theorem only
through the Commit-C contradiction. -/
theorem
    QsOtherFacetPlanarHighestPairSlicePackage.pr_nontrivial_actualRankTwoHessianChart_after_tiltedClosure
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
        T.terminal.blocker.presented) := by
  rcases S.pr_nontrivial_after_tiltedClosure
      hthree houtThree hnontrivial with ⟨R, hunit | hright⟩
  · rcases hunit with ⟨Q⟩
    rcases S.pr_unitContactFrontier R Q hthree houtThree hnontrivial with
      hleft | hright
    · rcases hleft with ⟨F⟩
      exact F.actualRankTwoHessianChart hthree houtThree
    · rcases hright with ⟨F⟩
      exact F.actualRankTwoHessianChart hthree houtThree
  · rcases hright with ⟨F⟩
    exact F.actualRankTwoHessianChart hthree houtThree

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
