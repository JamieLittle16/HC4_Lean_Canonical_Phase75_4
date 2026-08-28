import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacet
import HC4.Newton.PositiveCoordinateSingularBoundaryVertex
import Mathlib.Tactic

/-!
# A19.68: the balance-free first-contact ray has an actual outside boundary stratum

A19.67 extracts an honest affine support ray from the genuine first-nonfacet
carrier without using torus balance.  The ray remains Hessian-singular and all
of its supported monomials are nonlinear.  It also retains an actual supported
exponent with positive contact coordinate.

The finite-support exposed-vertex theorem can therefore be forced to expose a
boundary exponent on the *outside* side of the original coordinate facet.  We
retain that literal exponent, its support membership and nonlinear degree, and
the balance-free rank-three/codimension-two split.

No cocharacter, torus balance, or synthetic endpoint is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Actual outside boundary stratum carried by one balance-free first-contact
ray. -/
structure AdaptiveAlignedSmithCanonicalZeroStrictLowBalanceFreeRayBoundaryData
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    {facet : ToricFacet}
    (D : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T facet) : Type where
  exponent : Fin 4 →₀ ℕ
  mem : exponent ∈ D.ray.face.support
  nonlinear : 3 ≤ HC4.Polynomial.ordinaryDegree4 exponent
  contact_pos :
    0 < exponent (HC4.Polynomial.facetOmittedCoordinate facet)
  boundary : HC4.Polynomial.MvExponentOnBoundary exponent
  stratum :
    (∃ next : ToricFacet,
        HC4.Newton.MvRankThreeOnFacet next exponent) ∨
      HC4.Newton.MvExponentOnCodimensionTwoBoundary exponent

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}
variable {facet : ToricFacet}

/-- The balance-free affine ray still has literal positive-coordinate support. -/
theorem ray_positiveCoordinateSupport_nonempty
    (D : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T facet) :
    (HC4.Newton.positiveCoordinateSupport
      (HC4.Polynomial.facetOmittedCoordinate facet) D.ray.face).Nonempty := by
  exact ⟨D.ray.outsideExponent,
    HC4.Newton.mem_positiveCoordinateSupport.mpr
      ⟨D.ray.outside_mem_face, D.ray.outside_coordinate_pos⟩⟩

/-- Construct the actual outside boundary exponent and classify it without
balance. -/
noncomputable def outsideBoundary
    (D : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T facet) :
    AdaptiveAlignedSmithCanonicalZeroStrictLowBalanceFreeRayBoundaryData D := by
  have hex := HC4.Newton.exists_nonlinear_boundary_exponent_with_coordinate_pos
    D.ray_hessian_zero D.ray_support_degree_ge_three
    D.ray_positiveCoordinateSupport_nonempty
  have hnonempty : Nonempty
      (AdaptiveAlignedSmithCanonicalZeroStrictLowBalanceFreeRayBoundaryData D) := by
    rcases hex with ⟨d, hd, hdeg, hdpos, hboundary⟩
    have hsplit :
        (∃ next : ToricFacet, HC4.Newton.MvRankThreeOnFacet next d) ∨
          HC4.Newton.MvExponentOnCodimensionTwoBoundary d :=
      HC4.Newton.mvBoundary_rankThreeFacet_or_codimensionTwo hboundary
    exact ⟨{
      exponent := d
      mem := hd
      nonlinear := hdeg
      contact_pos := hdpos
      boundary := hboundary
      stratum := hsplit
    }⟩
  exact Classical.choice hnonempty

/-- In the rank-three alternative the outside boundary facet is genuinely
new: its omitted coordinate cannot be the original contact coordinate because
the exposed exponent is strictly positive there. -/
theorem outsideBoundary_rankThree_omitted_ne_contact
    (D : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T facet)
    (next : ToricFacet)
    (hthree : HC4.Newton.MvRankThreeOnFacet next D.outsideBoundary.exponent) :
    HC4.Polynomial.facetOmittedCoordinate next ≠
      HC4.Polynomial.facetOmittedCoordinate facet := by
  intro heq
  have hz :
      D.outsideBoundary.exponent
        (HC4.Polynomial.facetOmittedCoordinate next) = 0 := by
    exact (HC4.Polynomial.onFacet_toToricExponent_iff next
      D.outsideBoundary.exponent).1 hthree.1
  rw [heq] at hz
  omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
