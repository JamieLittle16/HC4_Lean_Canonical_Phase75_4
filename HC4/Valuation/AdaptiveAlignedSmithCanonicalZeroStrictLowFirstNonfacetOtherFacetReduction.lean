import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCodimensionTwoElimination
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowQsBoundaryClosure
import Mathlib.Tactic

/-!
# A19.92: the lower `qs` boundary has only the different-facet branch

A19.80 packages the genuine lower first-contact ray into three boundary
possibilities: its starting endpoint is codimension two, its actual outside
endpoint is rank three on a different coordinate facet, or that outside
endpoint is codimension two.

Under the surviving rank-three `.qs` hypothesis, the first possibility is
impossible because the starting endpoint has coordinate `0` equal to zero and
all three transverse coordinates strictly positive.  A19.91 eliminates the
far codimension-two endpoint.  Thus the lower boundary package now has one
honest survivor only: the actual unit outside endpoint is rank three on
`.pr`, `.sp`, or `.rq`.

This is a logical compression only.  It introduces no balance relation and no
new descent measure.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

private theorem qs_rankThree_not_codimensionTwo
    {d : Fin 4 →₀ ℕ}
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs d) :
    ¬ HC4.Newton.MvExponentOnCodimensionTwoBoundary d := by
  intro htwo
  rcases HC4.Newton.mvRankThreeOnFacet_qs hthree with ⟨h0, h1, h2, h3⟩
  rcases htwo with ⟨i, j, hij, hi, hj⟩
  fin_cases i <;> fin_cases j <;> simp_all

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- **A19.92 lower boundary compression.**  Once the starting endpoint is
rank three on `.qs`, every retained lower-boundary outcome places the actual
outside endpoint rank three on a different coordinate facet. -/
theorem qs_ray_boundaryOutcome_otherFacet
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtcome :
      AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.QsLowerBoundaryOutcome C) :
    ∃ next : ToricFacet,
      next ≠ .qs ∧
        HC4.Newton.MvRankThreeOnFacet next C.ray.outsideExponent := by
  rcases houtcome with hfacetTwo | houtThree | houtTwo
  · exact (qs_rankThree_not_codimensionTwo hthree hfacetTwo).elim
  · exact houtThree
  · exact (C.qs_ray_outside_codimensionTwo_impossible hthree houtTwo).elim

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
