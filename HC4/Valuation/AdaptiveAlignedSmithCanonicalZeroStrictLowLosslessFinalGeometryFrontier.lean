import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalGeometryFrontier
import Mathlib.Tactic

/-!
# Lossless final geometry frontier for the zero strict-low terminal

The first assembly-facing `FinalGeometryFrontier` intentionally compressed the
A19.71 nested disjunction, but its two transition constructors forgot one
useful piece of provenance: the rank-three certificate of the *starting*
exposed boundary exponent.

That certificate is exactly what later finite-support transition consumers
need in order to know which coordinate is positive when a second facet is
reached.  This module repeats only the final case split while retaining that
proof.  No new geometry, support claim, or terminal hypothesis is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- A provenance-complete version of the A19.71 final frontier. -/
inductive LosslessFinalGeometryFrontier
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Type (u + 1)
  | topBoundaryTransition
      (facet : ToricFacet)
      (rankThree :
        MvRankThreeOnFacet facet T.exposedSingularBoundaryVertex.exponent)
      (transition :
        AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryTransition
          facet T.topFace.face)
  | lowerBoundaryTransition
      (facet : ToricFacet)
      (rankThree :
        MvRankThreeOnFacet facet T.exposedSingularBoundaryVertex.exponent)
      (C :
        AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
          (K := K) T facet)
      (transition :
        AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryTransition
          facet C.face)
  | codimensionTwo
      (hcodim :
        MvExponentOnCodimensionTwoBoundary
          T.exposedSingularBoundaryVertex.exponent)
      (geometry : T.ExposedCodimensionTwoResolvedRankTwoGeometry)
  | quadraticSquare
      (facet : ToricFacet)
      (rankThree :
        MvRankThreeOnFacet facet T.exposedSingularBoundaryVertex.exponent)
      (d : Fin 4 →₀ ℕ)
      (mem : d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support)
      (degree_two : HC4.Polynomial.ordinaryDegree4 d = 2)
      (omitted_two : d (HC4.Polynomial.facetOmittedCoordinate facet) = 2)
      (pure :
        ∀ i : Fin 4, i ≠ HC4.Polynomial.facetOmittedCoordinate facet → d i = 0)
  | nonlinearConfined
      (facet : ToricFacet)
      (rankThree :
        MvRankThreeOnFacet facet T.exposedSingularBoundaryVertex.exponent)
      (confined :
        ∀ d ∈ (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family).support,
          3 ≤ HC4.Polynomial.ordinaryDegree4 d →
            HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d))

/-- Proposition-valued construction of the lossless frontier. -/
private theorem losslessFinalGeometryFrontier_nonempty
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    Nonempty T.LosslessFinalGeometryFrontier := by
  rcases T.exposedBoundary_rankThreeFacet_or_codimensionTwo with
    hthree | hcodim
  · rcases hthree with ⟨facet, hfacet⟩
    rcases T.rankThree_boundaryTransition_or_quadraticSquare_or_nonlinearConfined
        facet hfacet with
      htop | hlower | hsquare | hconfined
    · exact ⟨.topBoundaryTransition facet hfacet htop⟩
    · rcases hlower with ⟨C, htransition⟩
      exact ⟨.lowerBoundaryTransition facet hfacet C htransition⟩
    · rcases hsquare with ⟨d, hd, hdeg, homit, hpure⟩
      exact ⟨.quadraticSquare facet hfacet d hd hdeg homit hpure⟩
    · exact ⟨.nonlinearConfined facet hfacet hconfined⟩
  · exact ⟨.codimensionTwo hcodim
      (T.exposedCodimensionTwo_resolvedRankTwoGeometry hcodim)⟩

/-- **Lossless final zero-strict-low frontier.** -/
noncomputable def losslessFinalGeometryFrontier
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    T.LosslessFinalGeometryFrontier :=
  Classical.choice (losslessFinalGeometryFrontier_nonempty T)

/-- Forgetting the retained starting rank-three proof recovers the older
assembly-facing frontier exactly at the level of constructors. -/
noncomputable def LosslessFinalGeometryFrontier.toFinalGeometryFrontier
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (G : T.LosslessFinalGeometryFrontier) :
    T.FinalGeometryFrontier := by
  cases G with
  | topBoundaryTransition facet _ transition =>
      exact .topBoundaryTransition facet transition
  | lowerBoundaryTransition facet _ C transition =>
      exact .lowerBoundaryTransition facet C transition
  | codimensionTwo hcodim geometry =>
      exact .codimensionTwo hcodim geometry
  | quadraticSquare facet _ d mem degree_two omitted_two pure =>
      exact .quadraticSquare facet d mem degree_two omitted_two pure
  | nonlinearConfined facet _ confined =>
      exact .nonlinearConfined facet confined

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
