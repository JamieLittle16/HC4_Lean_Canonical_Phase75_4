import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowQsBoundaryClosure
import HC4.Newton.SingularBoundaryRankSplit
import Mathlib.Tactic

/-!
# A19.86: the `qs` quadratic-square residual is already codimension two

A19.80 leaves the exposed `.qs` rank-three branch as either a genuine lower
first-contact boundary outcome or a literal quadratic square in the omitted
coordinate.  In the `.qs` chart the omitted coordinate is `0`, so that square
has exponent `(2,0,0,0)`.  It therefore already lies on a codimension-two
coordinate boundary (in fact on three coordinate hyperplanes).

This file folds that syntactic square alternative into the same honest
codimension-two support frontier.  It does not claim that one codimension-two
monomial is by itself a planar terminal; the later adapter must still build the
full two-zero carrier required by the doubling/planar machinery.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- A literal omitted-coordinate quadratic square in the `.qs` chart is an
actual supported codimension-two exponent. -/
theorem qs_quadraticSquare_source_codimensionTwo
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ (polynomialFamilySpecialFiber
      T.terminal.blocker.presented.family).support)
    (hdeg : HC4.Polynomial.ordinaryDegree4 d = 2)
    (hsquare : d (HC4.Polynomial.facetOmittedCoordinate .qs) = 2)
    (hother : ∀ i : Fin 4,
      i ≠ HC4.Polynomial.facetOmittedCoordinate .qs → d i = 0) :
    d ∈ (polynomialFamilySpecialFiber
        T.terminal.blocker.presented.family).support ∧
      HC4.Polynomial.ordinaryDegree4 d = 2 ∧
      HC4.Newton.MvExponentOnCodimensionTwoBoundary d := by
  refine ⟨hd, hdeg, ?_⟩
  refine ⟨(1 : Fin 4), (2 : Fin 4), by decide, ?_, ?_⟩
  · exact hother (1 : Fin 4) (by decide)
  · exact hother (2 : Fin 4) (by decide)

/-- **A19.86 `.qs` residual compression.**  The literal quadratic-square
branch of A19.80 is not a separate geometry: it is already supported
codimension-two data. -/
theorem qs_rankThree_lowerBoundary_or_codimensionTwoSource
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs
      T.exposedSingularBoundaryVertex.exponent) :
    (∃ C :
        AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
          (K := K) T .qs,
        QsLowerBoundaryOutcome C) ∨
      (∃ d ∈ (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family).support,
        HC4.Polynomial.ordinaryDegree4 d = 2 ∧
          HC4.Newton.MvExponentOnCodimensionTwoBoundary d) := by
  rcases T.qs_rankThree_lowerBoundary_or_quadraticSquare hthree with
    hlower | hsquare
  · exact Or.inl hlower
  · rcases hsquare with ⟨d, hd, hdeg, hsq, hother⟩
    right
    refine ⟨d, ?_⟩
    exact T.qs_quadraticSquare_source_codimensionTwo hd hdeg hsq hother

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
