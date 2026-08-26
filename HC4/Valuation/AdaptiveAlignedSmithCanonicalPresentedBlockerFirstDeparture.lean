import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentedBoundaryEndpoint
import HC4.Valuation.AdaptiveAlignedSmithFirstLongitudinalDeparture

/-!
# A18.5.88: first longitudinal departure on the represented blocker fibre

The canonical blocker already carries a first positive later longitudinal
layer over its exact Smith exponent.  For final terminal assembly we must state
that certificate on the polynomial actually represented by the terminal state,
not behind the historical aligned-endpoint wrapper.

`AdaptiveAlignedSmithCanonicalPresentedBlocker.family_eq` is exactly the
provenance needed for this transport; no new geometric hypothesis is added.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- **A18.5.88 — a presented blocker retains its canonical first longitudinal
departure on the represented special fibre after the fixed right recentering.** -/
theorem AdaptiveAlignedSmithCanonicalPresentedBlocker.firstLongitudinalDeparture_on_presentedSpecialFiber
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source) :
    HasFirstExactSmithExponentLongitudinalDeparture
      (longitudinalRightRecenterHom
        (K := K) (polynomialFamilySpecialFiber D.presented.family))
      D.blocker.exponent := by
  have h := D.blocker.firstLongitudinalDeparture
  simpa [AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber, D.family_eq] using h

end

end HC4.Valuation
