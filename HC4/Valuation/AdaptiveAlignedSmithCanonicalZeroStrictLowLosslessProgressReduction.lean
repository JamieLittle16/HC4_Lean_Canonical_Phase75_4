import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowLosslessFinalGeometryFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopBoundaryRankTwoClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowQsRankTwoClosure
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowNonlinearConfinementHessian
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowActualRankThreeProgress
import Mathlib.Tactic

/-!
# Consume every already-source-rank-two branch of the lossless strict-low frontier

The provenance-complete A19 frontier still has five syntactic constructors,
but several are no longer genuine final obligations.

* a top-boundary transition is already either an actual represented-source
  rank-two Hessian chart or explicit codimension-two ray data;
* if the retained starting facet is the canonical `.qs` facet, the complete
  lower-boundary analysis now gives an actual represented-source rank-two
  chart unconditionally;
* complete nonlinear confinement gives an actual represented-source rank-two
  chart by the zero-defect Hessian argument.

Every actual source chart is immediately fed through the geometry-backed
`1 -> 2 -> 3` assembly.  This file therefore exports the genuinely smaller
residual frontier without treating any repair tag, auxiliary Rees layer, or
codimension-two support witness as a contradiction.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Geometry which genuinely survives after all currently available
represented-source rank-two consumers are applied. -/
inductive LosslessProgressResidual
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Type (u + 1)
  | topBoundaryCodimensionTwo
      (facet : ToricFacet)
      (rankThree :
        MvRankThreeOnFacet facet T.exposedSingularBoundaryVertex.exponent)
      (residual : T.TopBoundaryCodimensionTwoResidual facet)
  | lowerBoundaryNonQs
      (facet : ToricFacet)
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
  | quadraticSquareNonQs
      (facet : ToricFacet)
      (facet_ne_qs : facet ≠ .qs)
      (rankThree :
        MvRankThreeOnFacet facet T.exposedSingularBoundaryVertex.exponent)
      (d : Fin 4 →₀ ℕ)
      (mem : d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support)
      (degree_two : ordinaryDegree4 d = 2)
      (omitted_two : d (facetOmittedCoordinate facet) = 2)
      (pure : ∀ i : Fin 4, i ≠ facetOmittedCoordinate facet → d i = 0)

/-- **Lossless strict-low progress reduction.**

Either the honest reached source already has a geometry-backed rank-three
global successor, or it lies in one of the explicit residual geometries above.
In particular nonlinear confinement and every `.qs` rank-three branch have
been removed from the final obligation. -/
theorem globalRankThreeProgress_or_losslessResidual
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        AdaptiveAlignedSmithCanonicalGlobalMacroProgress target state) ∨
      Nonempty T.LosslessProgressResidual := by
  cases T.losslessFinalGeometryFrontier with
  | topBoundaryTransition facet rankThree transition =>
      rcases T.topBoundaryTransition_actualRankTwo_or_codimensionTwo
          facet rankThree transition with hactual | hcodim
      · rcases hactual with ⟨C⟩
        exact Or.inl (T.exists_globalRankThreeProgress_of_actualRankTwo C)
      · rcases hcodim with ⟨R⟩
        exact Or.inr ⟨.topBoundaryCodimensionTwo facet rankThree R⟩

  | lowerBoundaryTransition facet rankThree C transition =>
      by_cases hqs : facet = .qs
      · subst facet
        rcases T.qs_rankThree_actualRankTwo_noSquare rankThree with ⟨A⟩
        exact Or.inl (T.exists_globalRankThreeProgress_of_actualRankTwo A)
      · exact Or.inr
          ⟨.lowerBoundaryNonQs facet hqs rankThree C transition⟩

  | codimensionTwo hcodim geometry =>
      exact Or.inr ⟨.codimensionTwo hcodim geometry⟩

  | quadraticSquare facet rankThree d mem degree_two omitted_two pure =>
      by_cases hqs : facet = .qs
      · subst facet
        rcases T.qs_rankThree_actualRankTwo_noSquare rankThree with ⟨A⟩
        exact Or.inl (T.exists_globalRankThreeProgress_of_actualRankTwo A)
      · exact Or.inr
          ⟨.quadraticSquareNonQs
            facet hqs rankThree d mem degree_two omitted_two pure⟩

  | nonlinearConfined facet rankThree confined =>
      rcases T.nonlinearConfined_actualRankTwoHessianChart facet confined with ⟨A⟩
      exact Or.inl (T.exists_globalRankThreeProgress_of_actualRankTwo A)

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
