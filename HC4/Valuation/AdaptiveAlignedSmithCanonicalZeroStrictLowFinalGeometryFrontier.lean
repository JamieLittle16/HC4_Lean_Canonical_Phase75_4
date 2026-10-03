import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTerminalResidualReduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowCodimensionTwoFinalGeometry
import Mathlib.Tactic

/-!
# Final source-honest geometry frontier for a zero strict-low terminal

The producer-free zero-clock strict-low terminal has already been reduced to
five residual themes by A19.71.  The same-carrier codimension-two theme has
since been completely analysed by the source-honest A19.55 kernel-opening
chain: it carries one of the explicit resolved rank-two geometries of
`ExposedCodimensionTwoResolvedRankTwoGeometry`.

This file performs only the missing assembly splice.  In particular:

* the two boundary-transition cases retain the exact polynomial carrier on
  which the transition was proved;
* the codimension-two case retains both the actual exposed boundary witness
  and its complete resolved geometry;
* the literal quadratic-square and nonlinear-confinement cases are unchanged.

No auxiliary Rees order is identified with the zero blocker clock, no
repair-only promotion is treated as a contradiction, and no generic JC2
fallback is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Exact assembly-facing residual after consuming the complete
same-carrier codimension-two geometry. -/
inductive FinalGeometryFrontier
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Type (u + 1)
  | topBoundaryTransition
      (facet : ToricFacet)
      (transition :
        AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryTransition
          facet T.topFace.face)
  | lowerBoundaryTransition
      (facet : ToricFacet)
      (C :
        AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
          (K := K) T facet)
      (transition :
        AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryTransition
          facet C.face)
  | codimensionTwo
      (hcodim :
        HC4.Newton.MvExponentOnCodimensionTwoBoundary
          T.exposedSingularBoundaryVertex.exponent)
      (geometry : T.ExposedCodimensionTwoResolvedRankTwoGeometry)
  | quadraticSquare
      (facet : ToricFacet)
      (d : Fin 4 →₀ ℕ)
      (mem : d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support)
      (degree_two : HC4.Polynomial.ordinaryDegree4 d = 2)
      (omitted_two :
        d (HC4.Polynomial.facetOmittedCoordinate facet) = 2)
      (pure :
        ∀ i : Fin 4,
          i ≠ HC4.Polynomial.facetOmittedCoordinate facet → d i = 0)
  | nonlinearConfined
      (facet : ToricFacet)
      (confined :
        ∀ d ∈ (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family).support,
          3 ≤ HC4.Polynomial.ordinaryDegree4 d →
            HC4.Toric.OnFacet facet (HC4.Polynomial.toToricExponent d))

/-- Proposition-valued wrapper for the final frontier construction.

The upstream residual reduction is a nested disjunction in `Prop`, so it
cannot be eliminated directly into the `Type`-valued frontier.  Packaging
the result as `Nonempty` keeps the case split proposition-valued; the public
constructor below then performs one classical choice. -/
private theorem finalGeometryFrontier_nonempty
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    Nonempty T.FinalGeometryFrontier := by
  rcases
      T.boundaryTransition_or_codimensionTwo_or_quadraticSquare_or_nonlinearConfined with
    htop | hlower | hcodim | hsquare | hconfined
  · rcases htop with ⟨facet, htransition⟩
    exact ⟨.topBoundaryTransition facet htransition⟩
  · rcases hlower with ⟨facet, C, htransition⟩
    exact ⟨.lowerBoundaryTransition facet C htransition⟩
  · exact ⟨.codimensionTwo hcodim
      (T.exposedCodimensionTwo_resolvedRankTwoGeometry hcodim)⟩
  · rcases hsquare with ⟨facet, d, hd, hdeg, homit, hpure⟩
    exact ⟨.quadraticSquare facet d hd hdeg homit hpure⟩
  · rcases hconfined with ⟨facet, hfacet⟩
    exact ⟨.nonlinearConfined facet hfacet⟩

/-- **Final zero-strict-low geometry frontier.**

A genuine zero-clock strict-low terminal is exhausted by the two honest
boundary-transition carriers, the fully resolved same-carrier codimension-two
geometry, a literal represented-source quadratic square, or complete
nonlinear source confinement to one coordinate facet. -/
noncomputable def finalGeometryFrontier
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    T.FinalGeometryFrontier :=
  Classical.choice (finalGeometryFrontier_nonempty T)

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
