import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetDegreeGap
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowQsSquareCodimensionTwo
import Mathlib.Tactic

/-!
# A19.85: rigidity below the unit lower first-contact endpoint

A19.75/A19.79 force the genuine lower `.qs` ray endpoint to have omitted
coordinate exactly one, while A19.82 retains the source-level first-contact
weight inequality.  Comparing any represented-source monomial with that
actual contact endpoint gives a sharper statement than mere degree maximality:

* an outside source monomial of the same ordinary degree must also have
  omitted coordinate exactly one;
* every source monomial with omitted coordinate at least two lies at a
  strictly smaller ordinary degree than the retained outside endpoint.

This is the source-layer separation needed to combine the unit affine endpoint
with the strict-low `X (X - 1)` residual factors.  It is a local consequence
of the already-constructed first-contact weight, not a new global termination
measure.
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

/-- A represented-source monomial leaving `.qs` at the same ordinary degree as
the unit first-contact endpoint must itself have longitudinal exponent one. -/
theorem qs_ray_source_zeroCoordinate_eq_one_of_degree_eq_outside
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ (polynomialFamilySpecialFiber
      T.terminal.blocker.presented.family).support)
    (hd0 : 0 < d (0 : Fin 4))
    (hdeg : HC4.Polynomial.ordinaryDegree4 d =
      HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent) :
    d (0 : Fin 4) = 1 := by
  have hle := C.source_contact_le hd
  have hout := C.ray_contact_eq
    C.ray.outsideExponent C.ray.outside_mem_face
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  change
    HC4.Newton.scaledContactExponentWeight
        (0 : Fin 4) C.scale C.bump d ≤
      ((C.scale * T.topFace.degree : ℕ) : ℤ) at hle
  change
    HC4.Newton.scaledContactExponentWeight
        (0 : Fin 4) C.scale C.bump C.ray.outsideExponent =
      ((C.scale * T.topFace.degree : ℕ) : ℤ) at hout
  unfold HC4.Newton.scaledContactExponentWeight at hle hout
  rw [hout0, hdeg] at hout hle
  push_cast at hle hout
  have hbump : (0 : ℤ) < (C.bump : ℤ) := by
    exact_mod_cast C.bump_pos
  have hd0Z : (1 : ℤ) ≤ (d (0 : Fin 4) : ℤ) := by
    exact_mod_cast hd0
  have hleOne : (d (0 : Fin 4) : ℤ) ≤ 1 := by
    nlinarith
  exact_mod_cast (show (d (0 : Fin 4) : ℤ) = 1 by omega)

/-- Every represented-source monomial with at least two copies of the marked
longitudinal variable lies strictly below the actual unit outside endpoint in
ordinary degree. -/
theorem qs_ray_source_degree_lt_outside_of_two_le_zeroCoordinate
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ (polynomialFamilySpecialFiber
      T.terminal.blocker.presented.family).support)
    (hd0 : 2 ≤ d (0 : Fin 4)) :
    HC4.Polynomial.ordinaryDegree4 d <
      HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent := by
  have hle := C.source_contact_le hd
  have hout := C.ray_contact_eq
    C.ray.outsideExponent C.ray.outside_mem_face
  have hout0 : C.ray.outsideExponent (0 : Fin 4) = 1 :=
    C.qs_ray_outside_zeroCoordinate_eq_one hthree
  change
    HC4.Newton.scaledContactExponentWeight
        (0 : Fin 4) C.scale C.bump d ≤
      ((C.scale * T.topFace.degree : ℕ) : ℤ) at hle
  change
    HC4.Newton.scaledContactExponentWeight
        (0 : Fin 4) C.scale C.bump C.ray.outsideExponent =
      ((C.scale * T.topFace.degree : ℕ) : ℤ) at hout
  unfold HC4.Newton.scaledContactExponentWeight at hle hout
  rw [hout0] at hout
  push_cast at hle hout
  have hscale : (0 : ℤ) < (C.scale : ℤ) := by
    exact_mod_cast C.scale_pos
  have hbump : (0 : ℤ) < (C.bump : ℤ) := by
    exact_mod_cast C.bump_pos
  have hd0Z : (2 : ℤ) ≤ (d (0 : Fin 4) : ℤ) := by
    exact_mod_cast hd0
  have hdegZ :
      (HC4.Polynomial.ordinaryDegree4 d : ℤ) <
        (HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent : ℤ) := by
    nlinarith
  exact_mod_cast hdegZ

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
