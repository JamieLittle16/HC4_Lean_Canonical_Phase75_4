import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowRankThreeBoundaryReduction
import Mathlib.Tactic

/-!
# A19.71: exhaustive balance-free zero strict-low terminal residual

A19.55 exposes a genuine nonlinear coordinate-boundary exponent of the actual
singular maximal ordinary top face.  Its balance-free boundary split is either
rank three on one coordinate facet or codimension two.  A19.70 has now
refined the entire rank-three half into four provenance-honest possibilities.

This file performs the missing assembly step.  The complete zero-clock
strict-low singular terminal therefore lies in exactly one of five explicit
residual themes:

* a genuine boundary transition on the actual maximal top face;
* a genuine boundary transition on an explicitly retained lower first-contact
  carrier;
* the originally exposed top-face exponent is codimension two;
* the represented source contains a literal quadratic square in the omitted
  coordinate of the starting rank-three facet; or
* every nonlinear represented-source monomial is confined to that facet.

No witness is transported between carriers.  No balance, homogeneity,
cocharacter, synthetic endpoint, or new termination relation is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- **A19.71 exhaustive zero strict-low terminal frontier.**

This is the assembly-facing form of A19.55 + A19.70.  In the lower-transition
branch the actual first-nonfacet carrier `C` is retained existentially, so the
transition is asserted only on the polynomial where it was proved. -/
theorem
    boundaryTransition_or_codimensionTwo_or_quadraticSquare_or_nonlinearConfined
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    (∃ facet : ToricFacet,
        AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryTransition
          facet T.topFace.face) ∨
      (∃ facet : ToricFacet,
        ∃ C :
            AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
              (K := K) T facet,
          AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryTransition
            facet C.face) ∨
      HC4.Newton.MvExponentOnCodimensionTwoBoundary
        T.exposedSingularBoundaryVertex.exponent ∨
      (∃ facet : ToricFacet,
        ∃ d ∈ (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family).support,
          HC4.Polynomial.ordinaryDegree4 d = 2 ∧
          d (HC4.Polynomial.facetOmittedCoordinate facet) = 2 ∧
          ∀ i : Fin 4,
            i ≠ HC4.Polynomial.facetOmittedCoordinate facet → d i = 0) ∨
      (∃ facet : ToricFacet,
        ∀ d ∈ (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family).support,
          3 ≤ HC4.Polynomial.ordinaryDegree4 d →
            HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d)) := by
  rcases T.exposedBoundary_rankThreeFacet_or_codimensionTwo with
    hthree | htwo
  · rcases hthree with ⟨facet, hfacet⟩
    rcases T.rankThree_boundaryTransition_or_quadraticSquare_or_nonlinearConfined
        facet hfacet with htop | hlower | hsquare | hconfined
    · exact Or.inl ⟨facet, htop⟩
    · rcases hlower with ⟨C, htransition⟩
      exact Or.inr (Or.inl ⟨facet, C, htransition⟩)
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨facet, hsquare⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨facet, hconfined⟩)))
  · exact Or.inr (Or.inr (Or.inl htwo))

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
