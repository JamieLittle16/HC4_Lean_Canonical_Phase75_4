import HC4.Valuation.AdaptiveAlignedSmithCanonicalSourceNativeFirstContactReduction
import HC4.Valuation.AdaptiveAlignedSmithRankOneClosingRelativeFirstLayer
import Mathlib.Tactic

/-!
# A19.42: source-honest relative first-contact reduction

The positive earlier-actual-layer residual from A19.41 must not expose the
selected positive coefficient against the whole family: a coefficient may
have a nonzero constant term and still carry the first positive actual layer.

The correct object is the already-green relative deformation

    P = P(0) + X^j Q,

where `j` is the least positive actual parameter order and the special fibre
of `Q` is exactly the genuine coefficient potential `P_j`.

This file packages that canonical factorisation on the actual terminal trace
state and changes only the final producer API.  No presentation, ramification,
or new descent relation is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Canonical source packet carried by the positive earlier-actual-layer
residual.  All fields are theorems of `ActualParameterLayer` and
`AdaptiveAlignedSmithRankOneClosingRelativeFirstLayer`; the record merely
keeps them together on the exact `state.family` seen by the reduced trace. -/
structure AdaptiveAlignedSmithCanonicalEarlierActualRelativeContactData
    (state : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  hasActual : HasPositiveActualParameterLayer state.family
  order_lt :
    firstPositiveActualParameterOrder state.family hasActual < state.rawDefect
  deformation : MvPolynomial (Fin 4) (Polynomial K)
  deformation_eq :
    deformation = firstActualDeformationFamily state.family hasActual
  factorisation :
    state.family =
      constantPolynomialFamily (polynomialFamilySpecialFiber state.family) +
        MvPolynomial.C
            (Polynomial.X ^ firstPositiveActualParameterOrder state.family hasActual) *
          deformation
  specialFiber :
    polynomialFamilySpecialFiber deformation =
      familyParameterLayer state.family
        (firstPositiveActualParameterOrder state.family hasActual)
  specialFiber_ne_zero :
    polynomialFamilySpecialFiber deformation ≠ 0

/-- The earlier-actual-layer branch canonically produces the relative packet;
there is no geometric choice here. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalEarlierActualRelativeContactData.ofEarlierActual
    (state : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hactual : HasPositiveActualParameterLayer state.family)
    (hearly :
      firstPositiveActualParameterOrder state.family hactual < state.rawDefect) :
    AdaptiveAlignedSmithCanonicalEarlierActualRelativeContactData state := by
  let Q := firstActualDeformationFamily state.family hactual
  refine {
    hasActual := hactual
    order_lt := hearly
    deformation := Q
    deformation_eq := rfl
    factorisation := ?_
    specialFiber := ?_
    specialFiber_ne_zero := ?_
  }
  · simpa [Q] using firstActualDeformationFamily_factorisation state.family hactual
  · simpa [Q] using firstActualDeformationFamily_specialFiber state.family hactual
  · rw [show polynomialFamilySpecialFiber Q =
        familyParameterLayer state.family
          (firstPositiveActualParameterOrder state.family hactual) by
      simpa [Q] using firstActualDeformationFamily_specialFiber state.family hactual]
    exact firstPositiveActualParameterLayer_ne_zero state.family hactual

/-- Final producer checklist with the earlier positive branch stated on the
correct relative deformation rather than an impossible whole-family exposure.
The other two fields are unchanged from the source-native seam. -/
structure AdaptiveAlignedSmithCanonicalRelativeFirstContactResidualProducer where
  blockerZeroStrictLow :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) state)
      (_geometry : AdaptiveAlignedSmithCanonicalPresentedBlockerAllRankThreeGeometry
        canonicalAdaptiveAlignedSmithRepairRanking D 0)
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

  positiveSpecialFiberLow :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (geometry : AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_hpositive : 0 < state.rawDefect)
      (L : CanonicalPositiveTransverseReesLowLayer
        state.rawDefect state.family)
      (_hspecial :
        L.exponent ∈ (polynomialFamilySpecialFiber state.family).support),
      Nonempty (AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K))

  positiveEarlierRelative :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hrepair : state.repair = rankOneRepairState 0)
      (geometry : AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_hpositive : 0 < state.rawDefect)
      (L : CanonicalPositiveTransverseReesLowLayer
        state.rawDefect state.family)
      (R : AdaptiveAlignedSmithCanonicalEarlierActualRelativeContactData state),
      Nonempty (AdaptiveAlignedSmithCanonicalHonestFirstContactEndpoint (K := K))

/-- The relative producer is sufficient for the already-green source-native
reduced-trace closure. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalRelativeFirstContactResidualProducer.toSourceNative
    (P : AdaptiveAlignedSmithCanonicalRelativeFirstContactResidualProducer
      (K := K)) :
    AdaptiveAlignedSmithCanonicalSourceNativeFirstContactResidualProducer
      (K := K) where
  blockerZeroStrictLow := by
    intro state hrepair D geometry hzero e he hpattern hdeparture
    exact P.blockerZeroStrictLow
      hrepair D geometry hzero e he hpattern hdeparture
  positiveSpecialFiberLow := by
    intro state hrepair geometry hpositive L hspecial
    exact P.positiveSpecialFiberLow
      hrepair geometry hpositive L hspecial
  positiveEarlierActualLayer := by
    intro state hrepair geometry hpositive L hactual hearly
    let R :=
      AdaptiveAlignedSmithCanonicalEarlierActualRelativeContactData.ofEarlierActual
        state hactual hearly
    exact P.positiveEarlierRelative hrepair geometry hpositive L R

/-- HC4 front door after correcting the positive earlier-actual-layer seam. -/
theorem gradient_injective_of_hessianDeterminant_one_of_JC2_of_relativeFirstContactProducer
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : AdaptiveAlignedSmithCanonicalRelativeFirstContactResidualProducer
      (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) :=
  gradient_injective_of_hessianDeterminant_one_of_JC2_of_sourceNativeFirstContactProducer
    hJC2 P.toSourceNative F hdet

end

end HC4.Valuation
