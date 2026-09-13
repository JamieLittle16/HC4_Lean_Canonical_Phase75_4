import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetSourceLayerRigidity
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRankThreeDegreeGap
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowSourceCodimensionTwo
import Mathlib.Tactic

/-!
# A19.89: the strict-low codimension-two source residual lies below the unit ray

The producer-free strict-low terminal already contains an actual nonlinear
codimension-two source monomial with longitudinal multiplicity at least two
(A19.87).  On a genuine lower `.qs` degree-one first-contact carrier, A19.85
says every source monomial with longitudinal multiplicity at least two lies
strictly below the retained unit outside endpoint in ordinary degree.

This file keeps those two facts on the same witness.  In the subcase where the
outside endpoint is itself rank three on a different coordinate facet, A19.88
adds a further two-degree drop from that endpoint to the old maximal top face;
therefore the strict-low codimension-two source witness lies at least three
ordinary degrees below the old top.

No new recursion, balance relation, or transport between polynomial carriers
is introduced: the residual witness remains a monomial of the represented
source throughout.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Every genuine lower `.qs` degree-one terminal retains an actual nonlinear
codimension-two source monomial strictly below its outside endpoint. -/
theorem qs_ray_strictLow_sourceCodimensionTwo_degree_lt_outside
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent) :
    ∃ d ∈ (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      2 ≤ d (0 : Fin 4) ∧
      HC4.Newton.MvExponentOnCodimensionTwoBoundary d ∧
      HC4.Polynomial.ordinaryDegree4 d <
        HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent := by
  rcases T.strictLow_sourceCodimensionTwo_two_le with
    ⟨d, hd, hdeg, hd0, hcodim⟩
  have hlt :=
    C.qs_ray_source_degree_lt_outside_of_two_le_zeroCoordinate
      hthree hd hd0
  exact ⟨d, hd, hdeg, hd0, hcodim, hlt⟩

/-- If the unit outside endpoint crosses to a different rank-three facet, the
same strict-low codimension-two source witness is at least three ordinary
degrees below the original maximal top face. -/
theorem qs_ray_rankThree_otherFacet_strictLow_source_degree_add_three_le_topFace
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (next : ToricFacet)
    (hne : next ≠ .qs)
    (houtThree : HC4.Newton.MvRankThreeOnFacet next C.ray.outsideExponent) :
    ∃ d ∈ (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      2 ≤ d (0 : Fin 4) ∧
      HC4.Newton.MvExponentOnCodimensionTwoBoundary d ∧
      HC4.Polynomial.ordinaryDegree4 d + 3 ≤ T.topFace.degree := by
  rcases C.qs_ray_strictLow_sourceCodimensionTwo_degree_lt_outside hthree with
    ⟨d, hd, hdeg, hd0, hcodim, hlt⟩
  have houtGap :=
    C.qs_ray_rankThree_otherFacet_degree_add_two_le_topFace
      hthree next hne houtThree
  refine ⟨d, hd, hdeg, hd0, hcodim, ?_⟩
  omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation