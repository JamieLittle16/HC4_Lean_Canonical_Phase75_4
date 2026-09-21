import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminal
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowPureResidualSupport
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowZeroClockNoClosingCarrier
import Mathlib.Tactic

/-!
# Final source-honest seam packet for the zero strict-low singular endpoint

The public HC4 reduction is now waiting on one local theorem: impossibility of
`AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData`.

This file introduces no new mathematics.  It only packages, on one retained
singular terminal, the already-green source data which the final contradiction
is allowed to consume:

* the literal represented special fibre and its exact axis gradient collision;
* represented raw defect zero and blocker clock zero;
* the concrete strict-low residual normal form;
* exact mixed-degree data and the first longitudinal departure;
* honest first-contact Hessian curvature;
* the exact-active zero-defect rank-three chart and its nonzero constant
  `3 x 3` Hessian minor;
* the genuine singular maximal ordinary top face;
* actual source support supplied by the three strict-low residual patterns; and
* the formal guard excluding reuse of the positive-clock direct-closing
  carrier.

The point is purely architectural: downstream work should be able to attack
the final determinant/first-contact algebra without reopening the A19
construction stack or accidentally appealing to repair bookkeeping.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

/-- The represented special fibre retained by the actual zero-clock blocker. -/
abbrev representedSpecialFiber
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : MvPolynomial (Fin 4) K :=
  polynomialFamilySpecialFiber T.terminal.blocker.presented.family

/-- The honest right-recentered represented special fibre used by the exact
mixed-degree and first-contact packages. -/
abbrev rightRecenteredSpecialFiber
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : MvPolynomial (Fin 4) K :=
  longitudinalRightRecenterHom (K := K) T.representedSpecialFiber

/-- Source-support alternative reconstructed from the concrete residual normal
form.  This is deliberately source-facing and does not identify the exposed
pure-axis condition with the pure-longitudinal Smith pattern. -/
inductive SourceSupportAlternative
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Prop
  | pureLongitudinal
      (hpattern : IsPureLongitudinalSmithPattern T.terminal.exponent)
      (hwitness :
        ∃ d ∈ T.representedSpecialFiber.support,
          3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
          0 < d (0 : Fin 4) ∧
          d (1 : Fin 4) = 0 ∧
          d (2 : Fin 4) = 0 ∧
          d (3 : Fin 4) = 0)
  | lowNegativeFirst
      (hpattern : IsLowNegativeFirstSmithPattern T.terminal.exponent)
      (hwitness :
        ∃ d ∈ T.representedSpecialFiber.support,
          3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
          0 < d (0 : Fin 4) ∧
          d (2 : Fin 4) = 1)
  | lowNegativeSecond
      (hpattern : IsLowNegativeSecondSmithPattern T.terminal.exponent)
      (hwitness :
        ∃ d ∈ T.representedSpecialFiber.support,
          3 ≤ HC4.Polynomial.ordinaryDegree4 d ∧
          0 < d (0 : Fin 4) ∧
          d (1 : Fin 4) = 1)

/-- **G0 final seam packet.**

Every field below is an already-proved fact on the same represented terminal.
No progress theorem, source-complexity interpretation, terminal cocharacter,
or JC2 input is added. -/
structure FinalSeamData
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Type (u + 1) where
  exactCollision :
    HasExactGradientCollision T.representedSpecialFiber
      (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
      (Fin.cons (1 : K) (fun _ : Fin 3 => 0))
  presentedZero :
    T.terminal.blocker.presented.rawDefect = 0
  blockerZero :
    T.terminal.blocker.blocker.aligned.endpoint.defect = 0
  residualNormalForm :
    AdaptiveAlignedSmithCanonicalZeroStrictLowResidualNormalForm
      T.representedSpecialFiber T.terminal.exponent
  mixedDegree :
    ExactSmithExponentMixedDegreeData
      T.rightRecenteredSpecialFiber T.terminal.exponent
  firstDeparture :
    HasFirstExactSmithExponentLongitudinalDeparture
      T.rightRecenteredSpecialFiber T.terminal.exponent
  firstContact :
    AdaptiveAlignedSmithCanonicalFirstContactHessianGeometry
      T.rightRecenteredSpecialFiber (0 : Fin 4)
  exactActiveRankThree :
    AdaptiveAlignedSmithCanonicalZeroDefectRankThreeGeometry
      T.terminal.blocker.presented 0
  constantThreeByThree :
    AdaptiveAlignedSmithCanonicalExactActiveThreeByThreeGeometry
      (T.terminal.blocker.zeroStrictLow_completeRankThreeGeometry
        0 T.terminal.source_zero).chart
  topFaceNonzero :
    T.topFace.face ≠ 0
  topFaceDegreeGeThree :
    3 ≤ T.topFace.degree
  topFaceHessianZero :
    HC4.Polynomial.hessianDeterminant T.topFace.face = 0
  sourceSupport :
    T.SourceSupportAlternative
  noClosingCarrier :
    ¬ Nonempty
      (AdaptiveAlignedSmithRankOneClosingSourceCarrier
        (T.terminal.blocker.strictLowBlocker
          T.terminal.exponent T.terminal.mem T.terminal.pattern))

/-- Assemble the final seam packet without proving any new mathematical fact. -/
noncomputable def finalSeamData
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    T.FinalSeamData := by
  have hpacket := T.zeroClockFirstContactPacket
  have haxis := T.terminal.blocker.blocker.aligned.rawSpecialFiber_axisData
  rcases haxis with ⟨hcollisionRaw, _hzeroRaw, _hvalueRaw⟩
  have hF :
      T.representedSpecialFiber =
        T.terminal.blocker.blocker.aligned.endpoint.rawSpecialFiber := by
    simp [representedSpecialFiber,
      AdaptiveAlignedSmithMinimalEndpoint.rawSpecialFiber,
      T.terminal.blocker.family_eq]
  have hcollision :
      HasExactGradientCollision T.representedSpecialFiber
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0)) := by
    simpa [hF] using hcollisionRaw
  have hsupport : T.SourceSupportAlternative := by
    rcases T.terminal.pattern with hpure | hfirst | hsecond
    · exact .pureLongitudinal hpure (T.pureLongitudinal_sourceSupport hpure)
    · exact .lowNegativeFirst hfirst (T.lowNegativeFirst_sourceSupport hfirst)
    · exact .lowNegativeSecond hsecond (T.lowNegativeSecond_sourceSupport hsecond)
  exact {
    exactCollision := hcollision
    presentedZero := hpacket.1
    blockerZero := hpacket.2.1
    residualNormalForm := hpacket.2.2.1
    mixedDegree := hpacket.2.2.2.1
    firstDeparture := hpacket.2.2.2.2.1
    firstContact := hpacket.2.2.2.2.2
    exactActiveRankThree :=
      T.terminal.blocker.zeroStrictLow_completeRankThreeGeometry
        0 T.terminal.source_zero
    constantThreeByThree := T.terminal.constantThreeByThreeGeometry
    topFaceNonzero := T.topFace_ne_zero
    topFaceDegreeGeThree := T.topFace_degree_ge_three
    topFaceHessianZero := T.topFace_hessianDeterminant_eq_zero
    sourceSupport := hsupport
    noClosingCarrier := T.terminal.strictLowBlocker_noClosingSourceCarrier
  }

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
