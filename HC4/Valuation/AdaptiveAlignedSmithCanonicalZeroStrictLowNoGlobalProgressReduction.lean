import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowLosslessFinalGeometryFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopBoundaryRankTwoClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowActualRankTwoProgress
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowQsNoGlobalProgress
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowNonlinearConfinementNoGlobalProgress
import Mathlib.Tactic

/-!
# Reduce the lossless zero-strict-low frontier at a genuine global terminal

The post-C endgame now has several branches which are already completely
consumable under a no-successor hypothesis:

* every exposed `.qs` rank-three branch is impossible;
* nonlinear confinement gives an actual represented-state rank-two chart and
  hence strict global progress;
* the rank-two side of a top-boundary transition likewise gives strict global
  progress.

This module performs only that assembly reduction.  It deliberately retains
the remaining source-honest residuals verbatim:

* a non-`.qs` top-boundary codimension-two residual;
* a non-`.qs` lower boundary transition;
* the fully resolved same-carrier codimension-two geometry; or
* a non-`.qs` literal quadratic-square source term.

No new algebra, repair-only transition, auxiliary clock, or JC2 fallback is
introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Exact residual left after consuming every currently certified
no-global-progress branch of the lossless A19 frontier. -/
inductive NoGlobalProgressResidual
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Type (u + 1)
  | topBoundaryCodimensionTwo
      (facet : HC4.Toric.ToricFacet)
      (facet_ne_qs : facet ≠ .qs)
      (rankThree :
        MvRankThreeOnFacet facet T.exposedSingularBoundaryVertex.exponent)
      (residual : Nonempty (T.TopBoundaryCodimensionTwoResidual facet))
  | lowerBoundaryTransition
      (facet : HC4.Toric.ToricFacet)
      (facet_ne_qs : facet ≠ .qs)
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
      (facet : HC4.Toric.ToricFacet)
      (facet_ne_qs : facet ≠ .qs)
      (rankThree :
        MvRankThreeOnFacet facet T.exposedSingularBoundaryVertex.exponent)
      (d : Fin 4 →₀ ℕ)
      (mem : d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support)
      (degree_two : HC4.Polynomial.ordinaryDegree4 d = 2)
      (omitted_two :
        d (HC4.Polynomial.facetOmittedCoordinate facet) = 2)
      (pure :
        ∀ i : Fin 4,
          i ≠ HC4.Polynomial.facetOmittedCoordinate facet → d i = 0)

/-- **Post-C no-successor reduction.**

At a genuine global terminal, every already-closed branch of the lossless
zero-strict-low frontier is contradictory.  The only surviving constructors
are the four explicit residual families above. -/
theorem noGlobalProgressResidual
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hterminal :
      ∀ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        ¬ AdaptiveAlignedSmithCanonicalGlobalMacroProgress target state) :
    Nonempty T.NoGlobalProgressResidual := by
  let G := T.losslessFinalGeometryFrontier
  cases G with
  | topBoundaryTransition facet hthree htransition =>
      by_cases hqs : facet = .qs
      · subst facet
        exact (T.qs_rankThree_impossible_of_no_globalProgress
          hthree hterminal).elim
      · rcases T.topBoundaryTransition_actualRankTwo_or_codimensionTwo
          facet hthree htransition with htwo | hcodim
        · rcases htwo with ⟨C⟩
          exact (T.impossible_of_actualRankTwo_of_no_globalProgress
            C hterminal).elim
        · exact ⟨.topBoundaryCodimensionTwo facet hqs hthree hcodim⟩
  | lowerBoundaryTransition facet hthree C htransition =>
      by_cases hqs : facet = .qs
      · subst facet
        exact (T.qs_rankThree_impossible_of_no_globalProgress
          hthree hterminal).elim
      · exact ⟨.lowerBoundaryTransition facet hqs hthree C htransition⟩
  | codimensionTwo hcodim geometry =>
      exact ⟨.codimensionTwo hcodim geometry⟩
  | quadraticSquare facet hthree d mem degree_two omitted_two pure =>
      by_cases hqs : facet = .qs
      · subst facet
        exact (T.qs_rankThree_impossible_of_no_globalProgress
          hthree hterminal).elim
      · exact ⟨.quadraticSquare facet hqs hthree d mem
          degree_two omitted_two pure⟩
  | nonlinearConfined facet _hthree confined =>
      exact (T.nonlinearConfined_impossible_of_no_globalProgress
        facet confined hterminal).elim

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
