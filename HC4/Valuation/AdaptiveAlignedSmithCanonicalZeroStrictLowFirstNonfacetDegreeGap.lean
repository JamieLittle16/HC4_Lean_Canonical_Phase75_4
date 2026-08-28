import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetDegreeOneMaximality
import Mathlib.Tactic

/-!
# A19.84: ordinary-degree gap at the genuine lower first-contact ray

The lower `.qs` first-contact carrier already stores the exact denominator-
cleared contact equation.  Its facet endpoint has omitted coordinate zero, so
that equation forces its ordinary degree to be exactly the maximal source
degree used to construct the contact.  Its retained outside endpoint has
positive omitted coordinate, so positivity of both the scale and bump forces
its ordinary degree to be strictly smaller.

Together with A19.83, every represented-source monomial that actually leaves
`.qs` therefore lies at or below this strict sub-top degree.  This is a local
first-contact degree gap only; it is not a second global termination measure.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- The endpoint on the starting `.qs` facet remains on the original maximal
ordinary-degree layer. -/
theorem qs_ray_facet_degree_eq_topFace
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) :
    HC4.Polynomial.ordinaryDegree4 C.ray.facetExponent = T.topFace.degree := by
  have hcontact :=
    C.ray_contact_eq C.ray.facetExponent C.ray.facet_mem_face
  have hzero : C.ray.facetExponent (0 : Fin 4) = 0 := by
    simpa [HC4.Polynomial.facetOmittedCoordinate] using
      C.ray.facet_coordinate_zero
  change
    HC4.Newton.scaledContactExponentWeight
        (0 : Fin 4) C.scale C.bump C.ray.facetExponent =
      ((C.scale * T.topFace.degree : ℕ) : ℤ) at hcontact
  unfold HC4.Newton.scaledContactExponentWeight at hcontact
  rw [hzero] at hcontact
  push_cast at hcontact
  have hscale : (0 : ℤ) < (C.scale : ℤ) := by
    exact_mod_cast C.scale_pos
  have hdegZ :
      (HC4.Polynomial.ordinaryDegree4 C.ray.facetExponent : ℤ) =
        (T.topFace.degree : ℤ) := by
    nlinarith
  exact_mod_cast hdegZ

/-- The actual retained outside endpoint occurs strictly below the original
maximal ordinary-degree layer. -/
theorem qs_ray_outside_degree_lt_topFace
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs) :
    HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent < T.topFace.degree := by
  have hcontact :=
    C.ray_contact_eq C.ray.outsideExponent C.ray.outside_mem_face
  change
    HC4.Newton.scaledContactExponentWeight
        (0 : Fin 4) C.scale C.bump C.ray.outsideExponent =
      ((C.scale * T.topFace.degree : ℕ) : ℤ) at hcontact
  exact HC4.Newton.contact_degree_lt
    C.scale_pos C.bump_pos C.ray.outside_coordinate_pos hcontact

/-- Under the rank-three `.qs` terminal hypothesis, every represented-source
monomial which leaves `.qs` is strictly sub-top-degree. -/
theorem qs_ray_source_positive_zero_degree_lt_topFace
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ (polynomialFamilySpecialFiber
      T.terminal.blocker.presented.family).support)
    (hd0 : 0 < d (0 : Fin 4)) :
    HC4.Polynomial.ordinaryDegree4 d < T.topFace.degree := by
  exact lt_of_le_of_lt
    (C.qs_ray_source_outside_degree_le hthree hd hd0)
    C.qs_ray_outside_degree_lt_topFace

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
