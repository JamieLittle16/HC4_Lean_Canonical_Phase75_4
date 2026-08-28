import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowCrossFacetBoundaryTransition
import Mathlib.Tactic

/-!
# A19.70: exact residual reduction of the rank-three zero strict-low boundary

A19.66 separates the rank-three singular-top-face branch into four honest
finite-support possibilities.  A19.69 consumes both cross-facet alternatives:
whether the crossing occurs already on the maximal singular top face or only
at the lower genuine first-contact carrier, it produces an actual nonlinear
boundary exponent outside the starting facet.

Thus the rank-three branch now has only three residual themes:

1. a genuine balance-free boundary transition to a different rank-three facet
   or to a codimension-two coordinate boundary;
2. a literal supported quadratic square in the omitted coordinate; or
3. complete confinement of every nonlinear source monomial to the facet.

No torus balance, cocharacter, or affine-line conclusion is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- A genuine balance-free boundary transition away from one starting facet. -/
def AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryTransition
    {K : Type u} [Field K]
    (facet : ToricFacet)
    (F : MvPolynomial (Fin 4) K) : Prop :=
  ∃ d ∈ F.support,
    3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
    0 < d (HC4.Polynomial.facetOmittedCoordinate facet) ∧
    ((∃ next : ToricFacet,
        next ≠ facet ∧ HC4.Newton.MvRankThreeOnFacet next d) ∨
      HC4.Newton.MvExponentOnCodimensionTwoBoundary d)

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- **A19.70 exact rank-three residual reduction.** -/
theorem rankThree_boundaryTransition_or_quadraticSquare_or_nonlinearConfined
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hthree : HC4.Newton.MvRankThreeOnFacet facet
      T.exposedSingularBoundaryVertex.exponent) :
    AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryTransition
        facet T.topFace.face ∨
      (∃ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        HC4.Polynomial.ordinaryDegree4 d = 2 ∧
        d (HC4.Polynomial.facetOmittedCoordinate facet) = 2 ∧
        ∀ i : Fin 4,
          i ≠ HC4.Polynomial.facetOmittedCoordinate facet → d i = 0) ∨
      (∀ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        3 ≤ HC4.Polynomial.ordinaryDegree4 d →
          HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d)) := by
  rcases T.rankThree_crossFacet_or_firstNonfacetCrossFacet_or_quadraticSquare_or_nonlinearConfined
      facet hthree with htopCross | hfirstCross | hsquare | hconfined
  · rcases htopCross with ⟨D⟩
    exact Or.inl (T.topFaceCrossFacet_boundaryTransition facet D)
  · rcases hfirstCross with ⟨C⟩
    rcases T.firstNonfacetCrossFacet_boundaryTransition facet C with
      ⟨d, hd, hdeg, hpos, hstratum⟩
    left
    exact ⟨d, C.crossFacet.support_subset hd, hdeg, hpos, hstratum⟩
  · exact Or.inr (Or.inl hsquare)
  · exact Or.inr (Or.inr hconfined)

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
