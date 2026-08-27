import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroBlockerCoreReduction
import HC4.Valuation.AdaptiveAlignedSmithFirstLongitudinalDeparture
import HC4.Newton.MixedDegreeFirstWallCompetition
import Mathlib.Tactic

/-!
# A19.48: a strict-low terminal exponent is itself a blocker

The final A19.47 seam still carried the first longitudinal departure belonging
to the blocker exponent originally chosen by the canonical classifier.  That
choice is irrelevant once an actual strict-low exponent `e` has been found on
the same represented special fibre.

The aligned endpoint already retains the normalized zero-jet collision data.
Therefore `e` itself may be installed as a blocker exponent on exactly the
same aligned endpoint.  The mixed-degree classifier reconstructs its honest
residual outcome, and the existing blocker theorem then supplies the first
longitudinal departure for `e` automatically.

This removes any dependence on which blocker witness happened to be selected
upstream.  The final local seam is now just

    zero source clock + represented strict-low support -> honest first contact.

No JC2 input and no endpoint construction is asserted in this file.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalPresentedBlocker

/-- Repackage any represented strict-low support exponent as an actual blocker
on the very same aligned endpoint. -/
noncomputable def strictLowBlocker
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
      (polynomialFamilySpecialFiber D.presented.family))
    (hpattern :
      IsPureLongitudinalSmithPattern e ∨
      IsLowNegativeFirstSmithPattern e ∨
      IsLowNegativeSecondSmithPattern e) :
    AdaptiveAlignedSmithBlockerEndpoint (K := K) source.degreeCap := by
  have heRaw :
      e ∈ smithProjectedSupport (1 : Fin 4) 2 3
        D.blocker.aligned.endpoint.rawSpecialFiber := by
    simpa [AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber, D.family_eq]
      using he
  have haxis := D.blocker.aligned.rawSpecialFiber_axisData
  rcases haxis with ⟨hcoll, hzero, hvalue⟩
  let houtcome :
      MixedDegreeSmithExponentOutcome
        D.blocker.aligned.endpoint.rawSpecialFiber e :=
    projectedSmithExponent_mixedDegreeOutcome
      D.blocker.aligned.endpoint.rawSpecialFiber e heRaw
      hcoll hzero hvalue
  exact {
    aligned := D.blocker.aligned
    exponent := e
    mem := heRaw
    level := by simp
    pattern := by
      rcases hpattern with hpure | hfirst | hsecond
      · exact Or.inl hpure
      · exact Or.inr (Or.inl hfirst)
      · exact Or.inr (Or.inr (Or.inl hsecond))
    outcome := houtcome
  }

/-- The strict-low blocker has exactly the same represented raw special fibre
as the original presented endpoint. -/
theorem strictLowBlocker_rawSpecialFiber
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
      (polynomialFamilySpecialFiber D.presented.family))
    (hpattern :
      IsPureLongitudinalSmithPattern e ∨
      IsLowNegativeFirstSmithPattern e ∨
      IsLowNegativeSecondSmithPattern e) :
    (D.strictLowBlocker e he hpattern).aligned.endpoint.rawSpecialFiber =
      polynomialFamilySpecialFiber D.presented.family := by
  simp [strictLowBlocker, AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber,
    D.family_eq]

/-- Consequently the first longitudinal departure is available for the
*actual strict-low exponent* rather than for an unrelated classifier choice. -/
theorem strictLowBlocker_firstLongitudinalDeparture
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3
      (polynomialFamilySpecialFiber D.presented.family))
    (hpattern :
      IsPureLongitudinalSmithPattern e ∨
      IsLowNegativeFirstSmithPattern e ∨
      IsLowNegativeSecondSmithPattern e) :
    HasFirstExactSmithExponentLongitudinalDeparture
      (longitudinalRightRecenterHom
        (K := K) (polynomialFamilySpecialFiber D.presented.family)) e := by
  have h := (D.strictLowBlocker e he hpattern).firstLongitudinalDeparture
  rw [D.strictLowBlocker_rawSpecialFiber e he hpattern] at h
  exact h

end AdaptiveAlignedSmithCanonicalPresentedBlocker

/-- The genuinely minimal final local interface: strict-low support at zero
source clock must produce the honest first-contact endpoint.  The departure is
now a theorem, not an input. -/
structure AdaptiveAlignedSmithCanonicalZeroStrictLowFirstContactProducer where
  zeroStrictLow :
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
        IsLowNegativeSecondSmithPattern e),
      Nonempty (AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K))

/-- A zero-strict-low producer fills the A19.47 core interface; the historical
blocker-departure argument is deliberately ignored because A19.48 reconstructs
the departure on the actual strict-low exponent itself. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalZeroStrictLowFirstContactProducer.toCoreProducer
    (P : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstContactProducer
      (K := K)) :
    AdaptiveAlignedSmithCanonicalZeroBlockerFirstContactCoreProducer (K := K) where
  blockerZeroStrictLow := by
    intro state hrepair D hzero e he hpattern _hdeparture
    exact P.zeroStrictLow hrepair D hzero e he hpattern

/-- A19.46 final episode outcome with no departure object in the remaining
local interface. -/
theorem AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace.globalProgress_or_honestFirstContact_of_zeroStrictLowProducer
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneReesReducedTrace
      canonicalAdaptiveAlignedSmithRepairRanking 0 source)
    (hsrepair : source.repair = rankOneRepairState 0)
    (P : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstContactProducer
      (K := K)) :
    (∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        AdaptiveAlignedSmithCanonicalGlobalMacroProgress
          target T.trace.reachedRankThree.state) ∨
      Nonempty (AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K)) :=
  T.globalProgress_or_honestFirstContact_of_coreProducer
    hsrepair P.toCoreProducer

end

end HC4.Valuation
