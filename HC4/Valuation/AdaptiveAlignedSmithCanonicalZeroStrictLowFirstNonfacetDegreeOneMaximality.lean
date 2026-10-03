import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetDegreeOnePencil
import Mathlib.Tactic

/-!
# A19.83: the lower degree-one contact is maximal among outside source degrees

A19.82 retains the genuine source `IsWeightLE` certificate produced by the
minimal first-contact selector.  A19.75/A19.79 show that in the surviving
lower `.qs` rank-three branch the retained ray endpoint has omitted coordinate
exactly one.

Consequently the denominator-cleared contact equation at that endpoint is

    scale * deg(outside) + bump = scale * topDegree.

Every represented-source monomial with positive coordinate `0` satisfies the
corresponding weak inequality.  Since its coordinate `0` is at least one and
both `scale` and `bump` are positive, its ordinary degree is at most the degree
of the retained outside endpoint.

This is the precise source-facing minimal-contact consequence needed by the
strict-low residual normal forms.  No balance relation and no new termination
measure is introduced.
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

/-- **Unit first-contact maximality.**  Once the genuine lower `.qs` terminal
has coefficient degree one, its retained outside endpoint has maximal ordinary
degree among all represented-source monomials that actually leave `.qs`. -/
theorem qs_ray_source_outside_degree_le
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ (polynomialFamilySpecialFiber
      T.terminal.blocker.presented.family).support)
    (hd0 : 0 < d (0 : Fin 4)) :
    HC4.Polynomial.ordinaryDegree4 d ≤
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
  have hd0Z : (1 : ℤ) ≤ (d (0 : Fin 4) : ℤ) := by
    exact_mod_cast hd0
  have hdeg :
      (HC4.Polynomial.ordinaryDegree4 d : ℤ) ≤
        (HC4.Polynomial.ordinaryDegree4 C.ray.outsideExponent : ℤ) := by
    nlinarith
  exact_mod_cast hdeg

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
