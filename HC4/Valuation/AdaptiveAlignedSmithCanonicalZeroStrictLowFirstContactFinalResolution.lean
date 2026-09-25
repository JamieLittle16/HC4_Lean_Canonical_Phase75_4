import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowPlanarFinalResolution
import HC4.Valuation.AdaptiveAlignedSmithCanonicalFirstContactEndpointReduction

/-!
# Zero-strict-low singular terminals through the mature first-contact endpoint

The current E-stage works on the geometry-rich
`AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData`.  This carrier
already retains exactly the zero-clock source inputs of the mature
`AdaptiveAlignedSmithCanonicalFirstContactResidualProducer`:

* canonical rank-one repair provenance;
* the actual presented blocker and its complete rank-three geometry;
* literal raw defect zero; and
* an actually represented strict-low Smith exponent together with its pattern.

The retained exponent need not be the blocker's canonical Smith exponent, so
this adapter deliberately uses the arbitrary-exponent first-contact producer
rather than the later constructor-refined interface.

Once that producer returns the mature honest first-contact endpoint, the
unconditional planar Keller collision extraction and the planar terminal lift
turn it immediately into the permitted
`AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution`.

This module is assembly only: it introduces no new endpoint hypothesis and no
new geometry.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- The mature arbitrary-exponent first-contact producer resolves one concrete
zero-strict-low singular terminal. -/
theorem exists_finalResolution_of_firstContactResidualProducer
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state)
    (P : AdaptiveAlignedSmithCanonicalFirstContactResidualProducer
      (K := K)) :
    Nonempty
      (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T) := by
  let PT :
      AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0 :=
    .blocker T.terminal.blocker T.geometry
  have he :
      T.terminal.exponent ∈
        smithProjectedSupport (1 : Fin 4) 2 3 PT.specialFiber := by
    simpa [PT,
      AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber,
      AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.presentedState]
      using T.terminal.mem
  rcases P.zeroStrictLow
      T.terminal.repair_eq
      PT
      T.terminal.source_zero
      T.terminal.exponent
      he
      T.terminal.pattern with
    ⟨E⟩
  rcases
      HC4.Newton.hasPlanarKellerCollision_exists_terminalAssociatedGradedCollisionData
        E.hasPlanarKellerCollision with
    ⟨A⟩
  exact ⟨.associatedGradedCollision A⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- Hence the mature first-contact producer implies the exact current E3/E4
final-resolution property. -/
theorem
    zeroStrictLowSingularFinalResolutionProperty_of_firstContactResidualProducer
    (P : AdaptiveAlignedSmithCanonicalFirstContactResidualProducer
      (K := K)) :
    AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolutionProperty
      (K := K) := by
  intro state T
  exact T.exists_finalResolution_of_firstContactResidualProducer P

/-- **Current-architecture conditional HC4 closure.**

Once the zero-strict-low source geometry supplies the mature first-contact
producer, planar JC2 closes every four-variable determinant-one Hessian
gradient through the new final-resolution interface. -/
theorem
    gradient_injective_of_hessianDeterminant_one_of_JC2_of_firstContactFinalResolution
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : AdaptiveAlignedSmithCanonicalFirstContactResidualProducer
      (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (HC4.Newton.mvGradientMap F) := by
  exact
    gradient_injective_of_hessianDeterminant_one_of_JC2_of_zeroStrictLowSingularFinalResolution
      hJC2
      (zeroStrictLowSingularFinalResolutionProperty_of_firstContactResidualProducer P)
      F hdet

end

end HC4.Valuation
