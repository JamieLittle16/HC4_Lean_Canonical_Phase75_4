import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesFinalOutcome
import Mathlib.Tactic

/-!
# A19.47: geometry-free zero-blocker core

A19.46 isolated a single local producer after all positive-defect rank-three
states were routed back into genuine global macro progress.  Its field still
accepted an `AllRankThreeGeometry` argument inherited from the trace-facing
case split.

At the surviving local branch the source clock is already literally zero.
Complete zero-defect rank-three geometry is therefore canonical from the
source state itself, and the supplied geometry object carries no additional
hypothesis needed by the remaining source-to-first-contact construction.

This file removes that redundant input.  The resulting one-field interface is
the exact mathematical seam left on the HC4 side:

* a represented canonical blocker;
* source raw defect zero;
* an actual strict-low Smith exponent on its represented special fibre; and
* the blocker's certified first longitudinal departure.

Nothing else is assumed.  In particular no endpoint, terminal cocharacter,
JC2 hypothesis, or presentation-scale progress is hidden in this interface.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Minimal local constructor still required after the complete A19.46 global
closure.  Zero-defect rank-three geometry is deliberately not an argument. -/
structure AdaptiveAlignedSmithCanonicalZeroBlockerFirstContactCoreProducer where
  blockerZeroStrictLow :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) state)
      (_hzero : state.rawDefect = 0)
      (e : SmithSupportExponent)
      (_he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
        (polynomialFamilySpecialFiber D.presented.family))
      (_hpattern :
        IsPureLongitudinalSmithPattern e ∨
        IsLowNegativeFirstSmithPattern e ∨
        IsLowNegativeSecondSmithPattern e)
      (_hdeparture :
        HasFirstExactSmithExponentLongitudinalDeparture
          (longitudinalRightRecenterHom
            (K := K) (polynomialFamilySpecialFiber D.presented.family))
          D.blocker.exponent),
      Nonempty (AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K))

/-- Forgetfully reinsert the trace-supplied rank-three witness.  The witness is
unused because raw defect zero already determines the required rank-three
geometry independently. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalZeroBlockerFirstContactCoreProducer.toZeroBlockerProducer
    (P : AdaptiveAlignedSmithCanonicalZeroBlockerFirstContactCoreProducer
      (K := K)) :
    AdaptiveAlignedSmithCanonicalZeroBlockerFirstContactProducer (K := K) where
  blockerZeroStrictLow := by
    intro state hrepair D _geometry hzero e he hpattern hdeparture
    exact P.blockerZeroStrictLow
      hrepair D hzero e he hpattern hdeparture

/-- Trace-facing A19.46 outcome with only the geometry-free core producer as
local input. -/
theorem AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.globalProgress_or_honestFirstContact_of_coreProducer
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0)
    (P : AdaptiveAlignedSmithCanonicalZeroBlockerFirstContactCoreProducer
      (K := K)) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        AdaptiveAlignedSmithCanonicalGlobalMacroProgress
          target T.trace.reachedRankThree.state) ∨
      Nonempty (AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K)) :=
  T.globalProgress_or_honestFirstContact hsrepair P.toZeroBlockerProducer

/-- Globally terminal form of the same exact reduction. -/
theorem AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.honestFirstContact_of_no_globalProgress_of_coreProducer
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0)
    (P : AdaptiveAlignedSmithCanonicalZeroBlockerFirstContactCoreProducer
      (K := K))
    (hterminal :
      ∀ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        ¬ AdaptiveAlignedSmithCanonicalGlobalMacroProgress
          target T.trace.reachedRankThree.state) :
    Nonempty (AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K)) :=
  T.honestFirstContact_of_no_globalProgress
    hsrepair P.toZeroBlockerProducer hterminal

end

end HC4.Valuation
