import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowQsBoundaryClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCodimensionTwoElimination
import Mathlib.Tactic

/-!
# A19.92: compress the exposed `qs` lower boundary frontier

A19.80 reduces the canonically exposed `qs` rank-three terminal to the genuine
lower first-contact carrier or the literal omitted-coordinate quadratic square.
For the lower carrier, the retained facet endpoint is either already
codimension two or rank three on `qs`.  In the latter case A19.76 puts the
actual unit outside endpoint on a different rank-three facet or in
codimension two, and A19.91 eliminates the codimension-two far endpoint.

This file keeps the rank-three hypothesis attached to the lower carrier while
performing that elimination.  The resulting assembly-facing frontier has only
three honest alternatives:

* the lower ray starts at a codimension-two endpoint;
* it starts rank three on `qs` and its actual outside endpoint is rank three
  on a different coordinate facet; or
* the represented source contains the literal coordinate-zero quadratic
  square already isolated by the low-degree split.

No balance relation and no new progress measure are introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- **A19.92 reduced exposed-`qs` frontier.**  The far codimension-two endpoint
has been eliminated; the two genuinely geometric lower outcomes retain the
actual first-contact carrier. -/
theorem qs_rankThree_startCodimensionTwo_or_otherFacet_or_quadraticSquare
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs
      T.exposedSingularBoundaryVertex.exponent) :
    (∃ C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
        (K := K) T .qs,
      HC4.Newton.MvExponentOnCodimensionTwoBoundary C.ray.facetExponent) ∨
    (∃ C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
        (K := K) T .qs,
      ∃ next : ToricFacet,
        HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent ∧
        next ≠ .qs ∧
        HC4.Newton.MvRankThreeOnFacet next C.ray.outsideExponent) ∨
    (∃ d ∈ (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support,
      HC4.Polynomial.ordinaryDegree4 d = 2 ∧
      d (0 : Fin 4) = 2 ∧
      ∀ i : Fin 4, i ≠ (0 : Fin 4) → d i = 0) := by
  rcases T.qs_rankThree_affineTerminal_or_codimensionTwo_or_quadraticSquare
      hthree with htop | hlower | hsquare
  · rcases htop with ⟨R, _hendpoint⟩
    exact (T.qs_topFace_ray_impossible hthree R).elim
  · rcases hlower with ⟨C, hfacet⟩
    rcases hfacet with hfacetThree | hfacetTwo
    · rcases C.qs_ray_outside_boundaryTransition hfacetThree with
        houtThree | houtTwo
      · rcases houtThree with ⟨next, hne, hnext⟩
        exact Or.inr (Or.inl ⟨C, next, hfacetThree, hne, hnext⟩)
      · exact (C.qs_ray_outside_codimensionTwo_impossible
          hfacetThree houtTwo).elim
    · exact Or.inl ⟨C, hfacetTwo⟩
  · exact Or.inr (Or.inr hsquare)

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
