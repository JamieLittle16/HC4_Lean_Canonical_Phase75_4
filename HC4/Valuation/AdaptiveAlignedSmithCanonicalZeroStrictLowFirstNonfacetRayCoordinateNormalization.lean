import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacet
import HC4.Newton.FiniteSupportCrossFacetRayCoordinatePermutation
import Mathlib.Tactic

/-!
# Normalize every lower first-nonfacet ray to the canonical contact chart

The lower A19 carrier is already an honest balance-free
`CrossFacetRayData`, but its contact coordinate is the omitted coordinate of
an arbitrary toric facet.  The generic source-renaming adapter in
`FiniteSupportCrossFacetRayCoordinatePermutation` now makes the mature
contact-`0` affine RationalRigidity terminal available uniformly.

This file is only the valuation-facing composition.  No terminal package,
Smith datum, or auxiliary clock is transported.
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
variable {facet : ToricFacet}

/-- **Arbitrary-facet lower ray enters the canonical affine RR terminal.**

After swapping the actual contact coordinate with coordinate `0` and
re-extracting the ray from the renamed source support, the endpoint is either
rank three on canonical `.qs` with the full general affine terminal
certificate, or genuinely codimension two. -/
theorem ray_renamedZero_terminalCertificate_or_codimensionTwo
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T facet) :
    let R0 := C.ray.renameContactToZero
    (MvRankThreeOnFacet .qs R0.facetExponent ∧
      HC4.RationalRigidity.HasRankThreePolynomialTerminalCertificate
        (phi := R0.zeroCoefficientPolynomial)
        ((R0.facetExponent 1 : ℕ) : K)
        ((R0.facetExponent 2 : ℕ) : K)
        ((R0.facetExponent 3 : ℕ) : K)
        (1 : K)
        (R0.zeroSlope (1 : Fin 4))
        (R0.zeroSlope (2 : Fin 4))
        (R0.zeroSlope (3 : Fin 4))) ∨
      MvExponentOnCodimensionTwoBoundary R0.facetExponent := by
  exact C.ray.renamedZero_terminalCertificate_or_codimensionTwo
    C.ray_hessian_zero

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
