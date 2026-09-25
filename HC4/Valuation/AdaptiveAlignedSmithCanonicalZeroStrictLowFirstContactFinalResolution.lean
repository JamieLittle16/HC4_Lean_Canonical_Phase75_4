import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowPlanarFinalResolution
import HC4.Valuation.AdaptiveAlignedSmithCanonicalConstructorFirstContactReduction

/-!
# Zero-strict-low singular terminals through the mature first-contact endpoint

The current E-stage works on the geometry-rich
`AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData`.  That carrier
already retains every source-side input demanded by the older constructor-
refined blocker-zero first-contact producer:

* canonical rank-one repair provenance;
* the actual presented blocker and its complete rank-three geometry;
* literal raw defect zero;
* the represented strict-low Smith exponent and its pattern; and
* the certified first longitudinal departure from the A19.52 packet.

Consequently no additional presentation adapter is needed.  If the remaining
E-stage geometry constructs the mature honest first-contact endpoint, the new
planar terminal lift turns it immediately into the permitted
`ZeroStrictLowSingularFinalResolution`.

This module is assembly only: it introduces no new endpoint hypothesis and no
new geometry.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- A constructor-refined first-contact producer already resolves one concrete
zero-strict-low singular terminal.

Only its blocker-zero field is used: all positive-clock producer fields are
irrelevant at this already-reached zero-clock carrier. -/
theorem exists_finalResolution_of_constructorFirstContactProducer
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (P : AdaptiveAlignedSmithCanonicalConstructorFirstContactResidualProducer
      (K := K)) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T) := by
  rcases P.blockerZeroStrictLow
      T.terminal.repair_eq
      T.terminal.blocker
      T.geometry
      T.terminal.source_zero
      T.terminal.exponent
      T.terminal.mem
      T.terminal.pattern
      T.zeroClockFirstContactPacket.2.2.2.2.1 with
    ⟨E⟩
  exact E.exists_zeroStrictLowSingularFinalResolution T

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Hence the constructor-refined first-contact producer implies the exact
current E3/E4 final-resolution property. -/
theorem
    zeroStrictLowSingularFinalResolutionProperty_of_constructorFirstContactProducer
    (P : AdaptiveAlignedSmithCanonicalConstructorFirstContactResidualProducer
      (K := K)) :
    AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolutionProperty
      (K := K) := by
  intro state T
  exact T.exists_finalResolution_of_constructorFirstContactProducer P

end

end HC4.Valuation
