import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowQsReducedLowerFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetActualRankTwo
import Mathlib.Tactic

/-!
# A19 exposed `qs` frontier after cyclic source-pivot closure

The reduced lower frontier previously retained an abstract rank-three endpoint
on a coordinate facet different from `.qs`.  A19.129 already lifts the cyclic
ray pivot to a nonzero Hessian principal minor of the represented special
fibre, and the cyclic chart adapter packages that minor as an actual rank-two
Hessian chart.

Thus the rank-three `qs` branch now has only three assembly-facing outcomes:

* the lower ray itself starts on a codimension-two boundary;
* actual rank-two Hessian geometry is already present on the represented state;
* the literal omitted-coordinate quadratic square remains.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- **A19 rank-three `.qs` frontier with the other-facet branch consumed.** -/
theorem qs_rankThree_startCodimensionTwo_or_actualRankTwo_or_quadraticSquare
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hthree : MvRankThreeOnFacet .qs
      T.exposedSingularBoundaryVertex.exponent) :
    (∃ C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
        (K := K) T .qs,
      MvExponentOnCodimensionTwoBoundary C.ray.facetExponent) ∨
      Nonempty
        (AdaptiveAlignedSmithCanonicalActualRankTwoHessianChart
          T.terminal.blocker.presented) ∨
      (∃ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        ordinaryDegree4 d = 2 ∧
        d (0 : Fin 4) = 2 ∧
        ∀ i : Fin 4, i ≠ (0 : Fin 4) → d i = 0) := by
  rcases T.qs_rankThree_startCodimensionTwo_or_otherFacet_or_quadraticSquare
      hthree with hstart | hother | hsquare
  · exact Or.inl hstart
  · rcases hother with ⟨C, next, hCthree, hne, hnext⟩
    exact Or.inr (Or.inl <|
      C.qs_ray_otherFacet_actualRankTwoHessianChart hCthree hne hnext)
  · exact Or.inr (Or.inr hsquare)

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
