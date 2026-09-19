import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowLosslessFinalGeometryFrontier
import HC4.Newton.FiniteSupportCrossFacetRayCoordinatePermutation
import Mathlib.Tactic

/-!
# Turn a top-face boundary transition into the next honest cross-facet ray

The lossless final frontier retains both pieces needed on the *same* singular
top-face carrier:

* the original exposed exponent is rank three on the starting facet; and
* a boundary transition supplies a supported exponent rank three on a
  different facet, or already codimension two.

In the different-facet branch the new rank-three exponent lies on the new
coordinate hyperplane, while the original rank-three exponent is positive in
that new omitted coordinate.  Thus the same singular top face has support on
both sides of the new facet and the generic balance-free ray extractor applies.

No terminal package is renamed here.  The resulting ray can subsequently be
normalised to contact coordinate zero by
`CrossFacetRayData.renameContactToZero`.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

private theorem rankThree_coordinate_pos_on_otherFacet
    {d : Fin 4 →₀ ℕ}
    {facet next : ToricFacet}
    (hthree : MvRankThreeOnFacet facet d)
    (hne : next ≠ facet) :
    0 < d (HC4.Polynomial.facetOmittedCoordinate next) := by
  have hcoords := (mvRankThreeOnFacet_iff facet d).1 hthree
  cases facet <;> cases next <;>
    simp [HC4.Polynomial.facetOmittedCoordinate] at hne hcoords ⊢ <;>
    tauto

private theorem rankThree_omittedCoordinate_zero
    {d : Fin 4 →₀ ℕ}
    {facet : ToricFacet}
    (hthree : MvRankThreeOnFacet facet d) :
    d (HC4.Polynomial.facetOmittedCoordinate facet) = 0 := by
  have hcoords := (mvRankThreeOnFacet_iff facet d).1 hthree
  cases facet <;>
    simpa [HC4.Polynomial.facetOmittedCoordinate] using hcoords.1

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- A top-face transition either already lands at codimension two, or exposes
a genuine balance-free ray across the newly reached rank-three facet on the
same singular top face. -/
theorem topBoundaryTransition_nextRay_or_codimensionTwo
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (hthree :
      MvRankThreeOnFacet facet T.exposedSingularBoundaryVertex.exponent)
    (htransition :
      AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryTransition
        facet T.topFace.face) :
    (∃ next : ToricFacet,
        next ≠ facet ∧
          Nonempty
            (CrossFacetRayData T.topFace.face
              (HC4.Polynomial.facetOmittedCoordinate next))) ∨
      (∃ d ∈ T.topFace.face.support,
        MvExponentOnCodimensionTwoBoundary d) := by
  rcases htransition with
    ⟨d, hd, _hdeg, _holdPos, hnext | hcodim⟩
  · rcases hnext with ⟨next, hne, hnextThree⟩
    have hd0 : d (HC4.Polynomial.facetOmittedCoordinate next) = 0 :=
      rankThree_omittedCoordinate_zero hnextThree
    have hstartMem :
        T.exposedSingularBoundaryVertex.exponent ∈ T.topFace.face.support :=
      T.exposedBoundary_exponent_mem_topFace
    have hstartPos :
        0 < T.exposedSingularBoundaryVertex.exponent
          (HC4.Polynomial.facetOmittedCoordinate next) :=
      rankThree_coordinate_pos_on_otherFacet hthree hne
    have hzero :
        (HC4.Newton.zeroCoordinateSupport
          (HC4.Polynomial.facetOmittedCoordinate next) T.topFace.face).Nonempty :=
      ⟨d, HC4.Newton.mem_zeroCoordinateSupport.mpr ⟨hd, hd0⟩⟩
    have hpos :
        (HC4.Newton.positiveCoordinateSupport
          (HC4.Polynomial.facetOmittedCoordinate next) T.topFace.face).Nonempty :=
      ⟨T.exposedSingularBoundaryVertex.exponent,
        HC4.Newton.mem_positiveCoordinateSupport.mpr ⟨hstartMem, hstartPos⟩⟩
    exact Or.inl
      ⟨next, hne, ⟨HC4.Newton.crossFacetRayData hzero hpos⟩⟩
  · exact Or.inr ⟨d, hd, hcodim⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
