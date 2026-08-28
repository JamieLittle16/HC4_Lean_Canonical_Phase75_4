import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacet
import HC4.Newton.PositiveCoordinateSingularBoundaryVertex
import HC4.Newton.SingularBoundaryRankSplit
import Mathlib.Tactic

/-!
# A19.69: honest cross-facet carriers force a new boundary stratum

A19.66 gives two balance-free ways a rank-three zero-clock top face can already
cross its starting coordinate facet: directly on the maximal singular face,
or on the genuine lower first-contact carrier.  A19.68 now lets us expose a
nonlinear boundary exponent while forcing its old omitted coordinate to stay
positive.

Consequently a rank-three boundary exponent selected from either cross-facet
carrier can never lie on the starting facet.  It is either rank three on a
*different* coordinate facet or it lies on a codimension-two coordinate
boundary.  This is the first genuine balance-free facet transition in the
final A19 splice.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Generic finite-support transition for one singular nonlinear cross-facet
carrier.  Positivity of the old omitted coordinate rules out returning to the
same rank-three facet. -/
theorem crossFacet_singularBoundaryTransition
    {F : MvPolynomial (Fin 4) K}
    (facet : ToricFacet)
    (hzero : HC4.Polynomial.hessianDeterminant F = 0)
    (hnonlinear : ∀ d ∈ F.support, 3 ≤ HC4.Polynomial.ordinaryDegree4 d)
    (D : HC4.Newton.CrossFacetInitialData F
      (HC4.Newton.crossFacetOppositeCoordinate
        (HC4.Polynomial.facetOmittedCoordinate facet))
      (HC4.Polynomial.facetOmittedCoordinate facet)) :
    ∃ d ∈ F.support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      0 < d (HC4.Polynomial.facetOmittedCoordinate facet) ∧
      ((∃ next : ToricFacet,
          next ≠ facet ∧ HC4.Newton.MvRankThreeOnFacet next d) ∨
        HC4.Newton.MvExponentOnCodimensionTwoBoundary d) := by
  have hout :
      (HC4.Newton.positiveCoordinateSupport
        (HC4.Polynomial.facetOmittedCoordinate facet) F).Nonempty := by
    exact ⟨D.outsideExponent,
      HC4.Newton.mem_positiveCoordinateSupport.mpr
        ⟨D.outside_mem, D.outside_coordinate_pos⟩⟩
  rcases HC4.Newton.exists_nonlinear_boundary_exponent_with_coordinate_pos
      hzero hnonlinear hout with
    ⟨d, hd, hdeg, hdpos, hboundary⟩
  refine ⟨d, hd, hdeg, hdpos, ?_⟩
  rcases HC4.Newton.mvBoundary_rankThreeFacet_or_codimensionTwo hboundary with
    hthree | htwo
  · rcases hthree with ⟨next, hnext⟩
    left
    refine ⟨next, ?_, hnext⟩
    intro heq
    subst next
    have hzeroCoord :
        d (HC4.Polynomial.facetOmittedCoordinate facet) = 0 := by
      have hcoords :=
        (HC4.Newton.mvRankThreeOnFacet_iff facet d).1 hnext
      cases facet <;> exact hcoords.1
    omega
  · exact Or.inr htwo

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- A direct cross-facet face of the retained maximal singular top face gives
an actual transition away from its starting facet. -/
theorem topFaceCrossFacet_boundaryTransition
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (D : HC4.Newton.CrossFacetInitialData T.topFace.face
      (HC4.Newton.crossFacetOppositeCoordinate
        (HC4.Polynomial.facetOmittedCoordinate facet))
      (HC4.Polynomial.facetOmittedCoordinate facet)) :
    ∃ d ∈ T.topFace.face.support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      0 < d (HC4.Polynomial.facetOmittedCoordinate facet) ∧
      ((∃ next : ToricFacet,
          next ≠ facet ∧ HC4.Newton.MvRankThreeOnFacet next d) ∨
        HC4.Newton.MvExponentOnCodimensionTwoBoundary d) := by
  exact crossFacet_singularBoundaryTransition
    facet T.topFace_hessianDeterminant_eq_zero
    T.topFace.face_support_degree_ge_three D

/-- The lower genuine first-contact carrier has the same balance-free boundary
transition, using the nonlinear-support fact retained in A19.67. -/
theorem firstNonfacetCrossFacet_boundaryTransition
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (facet : ToricFacet)
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      (K := K) T facet) :
    ∃ d ∈ C.face.support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
      0 < d (HC4.Polynomial.facetOmittedCoordinate facet) ∧
      ((∃ next : ToricFacet,
          next ≠ facet ∧ HC4.Newton.MvRankThreeOnFacet next d) ∨
        HC4.Newton.MvExponentOnCodimensionTwoBoundary d) := by
  exact crossFacet_singularBoundaryTransition
    facet C.hessian_zero C.support_degree_ge_three C.crossFacet

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
