import HC4.Newton.ProductCoordinateHessian
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetRayReverseRees
import Mathlib.Tactic

/-!
# The actual terminal source cannot depend only on x, y, and z*w

Consumes the retained ray monomial on the actual determinant-one source.
If all source layers admit the product-coordinate representation, the new
source Hessian factorization contradicts that monomial. No equality between
the source and its initial ray, or between their clocks, is asserted.

The missing support argument would have to force this representation (or
exclude the actual layers that fail it). This theorem does not supply it.
-/

namespace HC4.Valuation
noncomputable section
open HC4.Newton HC4.Polynomial HC4.Toric

variable {K : Type*} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- A whole-source product-coordinate representation is impossible for the
retained rank-three `.qs` ray, including all later source layers. -/
theorem QsOtherFacetRayReverseReesPackage.source_ne_productCoordinateLift
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    (R : QsOtherFacetRayReverseReesPackage C)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (f : MvPolynomial (Fin 3) K) :
    polynomialFamilySpecialFiber T.terminal.blocker.presented.family ≠
      productCoordinateLift f := by
  intro heq
  have hcoeff := MvPolynomial.mem_support_iff.mp C.ray.facet_mem_face
  rw [← R.initialForm_eq_ray, HC4.Polynomial.coeff_initialForm] at hcoeff
  have hsource : MvPolynomial.coeff C.ray.facetExponent
      (productCoordinateLift f) ≠ 0 := by
    split_ifs at hcoeff
    · simpa [heq] using hcoeff
    · exact (hcoeff rfl).elim
  have hdet : hessianDeterminant (productCoordinateLift f) = 1 := by
    rw [← heq]
    exact T.terminal.blocker.presented.zeroDefect_specialFiber_hessianDeterminant_eq_one
      T.presented_zero
  have hfacet := mvRankThreeOnFacet_qs hthree
  have hexp := productCoordinate_supported_exponent_eq_product f hdet
    C.ray.facetExponent hsource hfacet.2.2.1
  have h1 := congrArg (fun e : Fin 4 →₀ ℕ => e 1) hexp
  have hpos := hfacet.2.1
  simp at h1
  omega

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
end
end HC4.Valuation
