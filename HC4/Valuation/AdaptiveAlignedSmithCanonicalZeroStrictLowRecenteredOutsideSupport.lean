import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowBoundaryStrata
import Mathlib.Tactic

/-!
# A19.57: the zero strict-low first departure gives actual outside support

A19.52 retains a genuine first later longitudinal layer on the literal
right-recentered represented special fibre.  For the finite-support
first-contact splice we need that information in the exact form consumed by
`FiniteSupportCrossFacetExposure`: a nonempty positive-coordinate support
slice.

This file performs only that conversion.  The witness is the actual later
support exponent supplied by `HasFirstExactSmithExponentLongitudinalDeparture`;
its longitudinal coordinate is positive because the departure offset is
strictly positive.  No top-face membership, facet crossing, balance, or new
endpoint is asserted here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open MvPolynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- The retained first longitudinal departure is literal support outside the
coordinate facet `d 0 = 0` of the right-recentered represented special fibre. -/
theorem recentered_positiveLongitudinalSupport_nonempty
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    (positiveCoordinateSupport (0 : Fin 4)
      (longitudinalRightRecenterHom
        (K := K)
        (polynomialFamilySpecialFiber
          T.terminal.blocker.presented.family))).Nonempty := by
  have hdeparture :
      HasFirstExactSmithExponentLongitudinalDeparture
        (longitudinalRightRecenterHom
          (K := K)
          (polynomialFamilySpecialFiber
            T.terminal.blocker.presented.family))
        T.terminal.exponent :=
    T.zeroClockFirstContactPacket.2.2.2.2.1
  rcases hdeparture.support_pair with ⟨n, q, hq, _hn, hnq⟩
  let d : Fin 4 →₀ ℕ :=
    (smithTransverseExponent
      T.terminal.exponent.b
      T.terminal.exponent.c
      T.terminal.exponent.d).cons (n + q)
  have hdpos : 0 < d (0 : Fin 4) := by
    have hnqpos : 0 < n + q := by omega
    simpa [d] using hnqpos
  exact ⟨d, mem_positiveCoordinateSupport.mpr ⟨by simpa [d] using hnq, hdpos⟩⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
