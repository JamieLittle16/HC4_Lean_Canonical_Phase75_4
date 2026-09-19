import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowQsActualRankTwoFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayFacetEndpointFirstBreakSourceLift
import Mathlib.Tactic

/-!
# A19 exposed `.qs` rank-three branch after rank-two closure

The reduced `.qs` frontier has three constructors:

* the retained lower ray starts at a codimension-two facet endpoint;
* cyclic source-pivot lifting already gives an actual represented-source
  rank-two Hessian chart; or
* the represented source contains the literal quadratic monomial `x₀²`.

The first constructor is no longer an unresolved boundary case.  The existing
lower-ray facet-endpoint theorem gives either an actual represented-source
rank-two chart or an honest reverse-Rees first-break packet carrying concrete
rank-two geometry.

This file is an assembly layer only.  It does not call auxiliary first-break
geometry an actual-state chart and it does not declare repair-only progress.
The only residual which is not already concrete rank-two geometry is the
literal `x₀²` source term.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Complete `.qs` rank-three frontier after consuming the cyclic
other-facet endpoint and the codimension-two lower-ray start into concrete
rank-two geometry. -/
inductive QsRankThreeRankTwoClosure
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Prop
  | actualRankTwo
      (C : Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented))
  | facetEndpointFirstBreak
      (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
        (K := K) T .qs)
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData.QsRayFacetEndpointFirstBreakData C))
  | quadraticSquare
      (d : Fin 4 →₀ ℕ)
      (mem : d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support)
      (degree_two : HC4.Polynomial.ordinaryDegree4 d = 2)
      (zero_two : d (0 : Fin 4) = 2)
      (other_zero : ∀ i : Fin 4, i ≠ (0 : Fin 4) → d i = 0)

/-- **A19 `.qs` rank-two closure.**

Every canonically exposed `.qs` rank-three strict-low terminal is already in
one of two concrete rank-two situations, except for the literal `x₀²`
source residual. -/
theorem qs_rankThree_rankTwoClosure
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hthree : MvRankThreeOnFacet .qs
      T.exposedSingularBoundaryVertex.exponent) :
    T.QsRankThreeRankTwoClosure := by
  rcases T.qs_rankThree_startCodimensionTwo_or_actualRankTwo_or_quadraticSquare
      hthree with hstart | htwo | hsquare
  · rcases hstart with ⟨C, _hcodim⟩
    rcases C.qs_ray_facetEndpoint_actualRankTwo_or_firstBreak with
      hactual | hbreak
    · exact .actualRankTwo hactual
    · exact .facetEndpointFirstBreak C hbreak
  · exact .actualRankTwo htwo
  · rcases hsquare with ⟨d, hd, hdeg, htwo, hother⟩
    exact .quadraticSquare d hd hdeg htwo hother



/-- Assembly-facing refinement of `QsRankThreeRankTwoClosure`.  The endpoint
first-break constructor is consumed one step further: instead of retaining an
auxiliary Rees packet, it exposes the exact weighted source component on which
the nonzero principal Hessian minor occurs. -/
inductive QsRankThreeSourceLiftedClosure
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Prop
  | actualRankTwo
      (C : Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented))
  | exactSourceWeightLayer
      (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
        (K := K) T .qs)
      (D :
        AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData.QsRayFacetEndpointFirstBreakData C)
      (layer :
        AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData.QsRayFacetEndpointFirstBreakData.ExactSourceWeightLayerMinorAtFirstBreak D)
  | quadraticSquare
      (d : Fin 4 →₀ ℕ)
      (mem : d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support)
      (degree_two : HC4.Polynomial.ordinaryDegree4 d = 2)
      (zero_two : d (0 : Fin 4) = 2)
      (other_zero : ∀ i : Fin 4, i ≠ (0 : Fin 4) → d i = 0)

/-- **Source-lifted `.qs` frontier.**  Every endpoint-first-break residue is
now represented directly by a weighted component of the actual source. -/
theorem qs_rankThree_sourceLiftedClosure
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hthree : MvRankThreeOnFacet .qs
      T.exposedSingularBoundaryVertex.exponent) :
    T.QsRankThreeSourceLiftedClosure := by
  cases T.qs_rankThree_rankTwoClosure hthree with
  | actualRankTwo C =>
      exact .actualRankTwo C
  | facetEndpointFirstBreak C hD =>
      rcases hD with ⟨D⟩
      rcases D.actualRankTwo_or_exactSourceWeightLayerMinor with
        hactual | hlayer
      · exact .actualRankTwo hactual
      · exact .exactSourceWeightLayer C D hlayer
  | quadraticSquare d mem degree_two zero_two other_zero =>
      exact .quadraticSquare d mem degree_two zero_two other_zero

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
