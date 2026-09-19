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

The large certificate is retained inside the compact Newton-level constructor,
avoiding repeated dependent normalization in valuation assembly. -/
theorem ray_renamedZeroTerminalOutcome
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T facet) :
    C.ray.RenamedZeroTerminalOutcome := by
  exact C.ray.renamedZeroTerminalOutcome C.ray_hessian_zero

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
