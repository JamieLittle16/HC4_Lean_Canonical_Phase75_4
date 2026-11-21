import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneReesLowLayerOrderReduction
import HC4.Valuation.AdaptiveAlignedSmithFirstContactTwoZeroJC2
import Mathlib.Tactic

/-!
# A19.36: one honest first-contact endpoint for the final residuals

The remaining source-facing residuals should not each invent their own
terminal representation.  The mature first-contact library already has the
honest polynomial endpoint:

* an actual blocker and its recentered source;
* a genuine positive first-contact lattice;
* terminal transformed Hessian clock zero;
* a polynomial Monge--Ampere fibre with a distinct exact gradient collision;
* a *second*, honest terminal source cocharacter transporting the marked right
  point.

The last item is intentionally not the exposure weight.  The first-contact
library proves those two weights cannot be identified.

This file packages that mature endpoint behind one uniform type.  Every such
endpoint has a marked zero terminal weight and, by the unconditional unique-zero
elimination, a second zero.  Thus its surviving weight pattern is exactly the
canonical two-zero branch consumed by A19.4 under planar JC2.

No endpoint producer is asserted here.  The three source-facing producer
fields below are the exact adapters A19.35/A19.36 still have to construct from
the retained HC4 descent provenance.  Keeping them separate from the endpoint
consumer prevents a terminal cocharacter from being manufactured by API
bookkeeping.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Uniform carrier for the genuine first-contact/two-zero endpoint already
formalized by the mature closing library. -/
structure AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint : Type (u + 1) where
  degreeCap : ℕ
  blocker : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap
  source : AdaptiveAlignedSmithBlockerRecenteredSourceData blocker
  terminal : AdaptiveAlignedSmithClosingFirstContactTerminalData blocker source
  cocharacter : AdaptiveAlignedSmithFirstContactTerminalCocharacterData terminal

namespace AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint

/-- Every honest endpoint has a second zero terminal weight unconditionally. -/
theorem hasSecondMarkedTerminalZero
    (E : AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K)) :
    E.cocharacter.HasSecondMarkedTerminalZero :=
  E.cocharacter.hasSecondMarkedTerminalZero

/-- Planar JC2 closes exactly this endpoint, and nowhere earlier in the new
A19.34b/A19.35 route. -/
theorem impossible_of_JC2
    (E : AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K))
    (hJC2 : HC4.PlanarJC2Injectivity K) :
    False :=
  E.cocharacter.impossible_of_JC2 hJC2

end AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint

/-- Exact producer checklist required to funnel the three presentation-free
A19.35 source residuals into the single honest first-contact endpoint.

These are deliberately producers of genuine data, rather than local `False`
obligations.  Once they are built, all three branches share one final theorem. -/
structure AdaptiveAlignedSmithCanonicalFirstContactResidualProducer where
  zeroStrictLow :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_hzero : state.rawDefect = 0)
      (e : SmithSupportExponent)
      (_he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
      (_hpattern :
        IsPureLongitudinalSmithPattern e ∨
        IsLowNegativeFirstSmithPattern e ∨
        IsLowNegativeSecondSmithPattern e),
      Nonempty (AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K))

  positiveSpecialFiberLow :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_hpositive : 0 < state.rawDefect)
      (L : CanonicalPositiveTransverseReesLowLayer
        state.rawDefect state.family)
      (_hspecial :
        L.exponent ∈ (polynomialFamilySpecialFiber state.family).support),
      Nonempty (AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K))

  positiveEarlierActualLayer :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_hpositive : 0 < state.rawDefect)
      (L : CanonicalPositiveTransverseReesLowLayer
        state.rawDefect state.family)
      (hactual : HasPositiveActualParameterLayer state.family)
      (_hearly :
        firstPositiveActualParameterOrder state.family hactual <
          state.rawDefect),
      Nonempty (AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K))

/-- A single impossibility theorem for the honest endpoint consumes all three
source-facing residual producers. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalFirstContactResidualProducer.toReesLowLayerOrderResidualResolver
    (P : AdaptiveAlignedSmithCanonicalFirstContactResidualProducer (K := K))
    (hendpoint :
      ∀ E : AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K),
        False) :
    AdaptiveAlignedSmithCanonicalReesLowLayerOrderResidualResolver (K := K) where
  zeroStrictLow := by
    intro state hrepair T hzero e he hpattern
    rcases P.zeroStrictLow hrepair T hzero e he hpattern with ⟨E⟩
    exact hendpoint E

  positiveSpecialFiberLow := by
    intro state hrepair T hpositive L hspecial
    rcases P.positiveSpecialFiberLow hrepair T hpositive L hspecial with ⟨E⟩
    exact hendpoint E

  positiveEarlierActualLayer := by
    intro state hrepair T hpositive L hactual hearly
    rcases P.positiveEarlierActualLayer
        hrepair T hpositive L hactual hearly with ⟨E⟩
    exact hendpoint E

/-- Unrestricted HC4 once the three source adapters and the single honest
first-contact endpoint theorem have both been completed. -/
theorem gradient_injective_of_hessianDeterminant_one_of_firstContactResidualProducer_of_endpointImpossible
    (P : AdaptiveAlignedSmithCanonicalFirstContactResidualProducer (K := K))
    (hendpoint :
      ∀ E : AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K),
        False)
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) := by
  exact
    gradient_injective_of_hessianDeterminant_one_of_reesLowLayerOrderResidualResolver
      (P.toReesLowLayerOrderResidualResolver hendpoint) F hdet

/-- Conditional audit theorem: once the three honest producers are available,
planar JC2 closes the *single* final endpoint via A19.4. -/
theorem gradient_injective_of_hessianDeterminant_one_of_JC2_of_firstContactResidualProducer
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : AdaptiveAlignedSmithCanonicalFirstContactResidualProducer (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) := by
  exact
    gradient_injective_of_hessianDeterminant_one_of_firstContactResidualProducer_of_endpointImpossible
      P (fun E => E.impossible_of_JC2 hJC2) F hdet

end

end HC4.Valuation
