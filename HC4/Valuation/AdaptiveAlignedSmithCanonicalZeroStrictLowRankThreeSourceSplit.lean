import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetSource
import Mathlib.Tactic

/-!
# A19.60: exact source split below the rank-three zero strict-low top face

A19.58 says that a rank-three exposed maximal-face exponent either already
produces a genuine cross-facet exact face, or the whole selected maximal face
is confined to its coordinate facet.  A19.59 then transports that confinement
back to the represented special fibre at the selected maximal degree.

The only remaining support question is whether some lower-degree nonlinear
source monomial leaves that facet.  This file makes that dichotomy explicit.
If such a monomial exists we retain the exact `HasNonlinearOutsideFacet`
interface consumed by the generic first-nonfacet selector.  Otherwise every
nonlinear source monomial is genuinely confined to the facet.

No low-degree tameness, torus balance, terminal cocharacter, or progress claim
is assumed or manufactured.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Assembly-facing exact trichotomy for a rank-three boundary exponent:

1. the maximal singular face already crosses its coordinate facet;
2. the maximal face is on the facet but lower nonlinear source support leaves
   it; or
3. every nonlinear source monomial is confined to the facet.
-/
theorem rankThree_crossFacet_or_nonlinearOutside_or_nonlinearConfined
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hthree : MvRankThreeOnFacet facet
      T.exposedSingularBoundaryVertex.exponent) :
    Nonempty
        (CrossFacetInitialData T.topFace.face
          (HC4.Newton.crossFacetOppositeCoordinate
            (HC4.Polynomial.facetOmittedCoordinate facet))
          (HC4.Polynomial.facetOmittedCoordinate facet)) ∨
      (HC4.Newton.HasNonlinearOutsideFacet facet
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) ∧
        HC4.Newton.TopDegreeOnFacet facet T.topFace.degree
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)) ∨
      (∀ d ∈
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family).support,
        3 ≤ HC4.Polynomial.ordinaryDegree4 d →
          HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d)) := by
  rcases T.rankThree_crossFacetInitial_or_topFaceOnFacet facet hthree with
    hcross | htop
  · exact Or.inl hcross
  · have htopSource :
        HC4.Newton.TopDegreeOnFacet facet T.topFace.degree
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family) :=
      T.topFaceOnFacet_topDegreeOnFacet facet htop
    by_cases hout :
        HC4.Newton.HasNonlinearOutsideFacet facet
          (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)
    · exact Or.inr (Or.inl ⟨hout, htopSource⟩)
    · right
      right
      intro d hd hnonlinear
      by_contra hnotFacet
      exact hout ⟨d, hd, hnonlinear, hnotFacet⟩

/-- In the middle branch all source-side hypotheses of
`exists_singular_first_nonfacet_contact` are already present except the
explicit low-degree-tameness condition. -/
theorem firstNonfacet_sourceCore
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hout : HC4.Newton.HasNonlinearOutsideFacet facet
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family))
    (htop : HC4.Newton.TopDegreeOnFacet facet T.topFace.degree
      (polynomialFamilySpecialFiber T.terminal.blocker.presented.family)) :
    3 ≤ T.topFace.degree ∧
      HC4.Newton.NonlinearDegreeBound T.topFace.degree
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) ∧
      HC4.Newton.TopDegreeOnFacet facet T.topFace.degree
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) ∧
      HC4.Newton.HasNonlinearOutsideFacet facet
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) ∧
      HC4.MongeAmpere.IsPolynomialMongeAmpere
        (polynomialFamilySpecialFiber T.terminal.blocker.presented.family) := by
  exact ⟨T.topFace_degree_ge_three,
    T.representedSpecialFiber_nonlinearDegreeBound_topFace,
    htop, hout, T.representedSpecialFiber_isPolynomialMongeAmpere⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
