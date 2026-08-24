import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalSurvivingGeometryReduction
import HC4.Valuation.AdaptiveKernelFreeFixedScaleProgress
import Mathlib.Tactic

/-!
# A18.4.11: consume every non-increasing surviving Smith exposure clock

A18.4.10 reduces the surviving-wall geometry to two actual coefficientwise
Smith exposures:

* a genuine marked-point boundary exposure;
* a canonical exposure whose special fibre is free of coordinate `3`.

The coefficientwise exposure is not automatically a pure ramification.  Its
exact determinant clock is

    R * Delta + 2 * sum W - 4 * m,

so it is unsound to discard the correction term.  This file handles that
clock exactly rather than pretending the exposure is zero-cost.

There are two sound consumption rules.

1. If a boundary exposure has clock strictly below `R * Delta`, the actual
   boundary-sheared family, recorded at the real absolute exposure scale, is
   already a certified ramified raw-defect spend.
2. If a kernel-free exposure has clock merely at most `R * Delta`, the
   already-proved saturated `x₃` kernel restart spends a positive amount after
   one further ramification.  Hence the *composite* is a certified ramified
   raw-defect spend even when the exposure clock itself is exactly neutral.

Thus the only exposure arithmetic left after this module is genuinely
one-sided:

* a boundary whose exposure clock is nondecreasing; or
* a kernel-free exposure whose clock strictly overshoots the pure-ramified
  aligned clock.

No quotient clock, rational well-foundedness claim, or repair-only successor
is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## A lowering boundary exposure is already a global strict macro -/

/-- If the actual coefficientwise Smith exposure strictly lowers the raw
clock relative to pure exposure ramification, then its determinant-one
boundary normalisation remains a genuine strict spend.  The aligned exact
clock presentation is prefixed afterwards, so the resulting macro starts at
`source` itself. -/
theorem AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint.globalRamifiedStrictMacro_of_exposureDefect_lt
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
      (K := K) source)
    (clock_eq :
      E.W.original.aligned.endpoint.defect =
        alignedSmithRamificationIndex * source.rawDefect)
    (hlt :
      E.exposure.defect <
        E.exposure.ramification.R *
          E.W.original.aligned.endpoint.defect) :
    AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source := by
  let outer := E.W.original.aligned.toOuterScaleAwareState source
  let B : AdaptiveSmithExposureSectionBoundary E.exposure :=
    Classical.choice E.boundary
  let boundaryState : AdaptiveGeometricRestartState (K := K) :=
    B.toAdaptiveState
  let target :=
    boundaryState.toScaleAwareAt
      (E.exposure.ramification.R * outer.scale)
      (Nat.mul_pos E.exposure.ramification.R_pos outer.scale_pos)

  have hsource : HasCertifiedRamifiedEpisodeInternalMove outer source := by
    exact
      ⟨E.W.original.aligned.certifiedOuterInternal_of_defect_eq
        source clock_eq⟩

  have hraw :
      target.rawDefect <
        E.exposure.ramification.R * outer.rawDefect := by
    simpa [target, boundaryState, outer,
      AdaptiveSmithExposureSectionBoundary.toAdaptiveState] using hlt

  have hspendOuter :
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target outer := by
    change Nonempty (CertifiedRamifiedRawDefectSpend target outer)
    exact
      ⟨{
        ramification := E.exposure.ramification.R
        ramification_pos := E.exposure.ramification.R_pos
        scale_eq := by rfl
        raw_lt := hraw
      }⟩

  have hspendSource := hsource.then_spend hspendOuter
  exact hspendSource.toGlobalStrictMacro RR

/-! ## A non-increasing kernel-free exposure followed by first contact is strict -/

/-- A kernel-free exposure need not itself lower the aligned clock.  Equality
is harmless: the saturated first `x₃` contact has positive slope and therefore
spends a positive raw-defect amount after its denominator-clearing
ramification.

The target returned by the local saturated stage is re-recorded only at its
*actual absolute scale*; its family and raw Hessian clock are unchanged. -/
theorem AdaptiveAlignedSmithCanonicalGlobalKernelFreeExposureEndpoint.globalRamifiedStrictMacro_of_exposureDefect_le
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (E : AdaptiveAlignedSmithCanonicalGlobalKernelFreeExposureEndpoint
      (K := K) source)
    (clock_eq :
      E.W.original.aligned.endpoint.defect =
        alignedSmithRamificationIndex * source.rawDefect)
    (hle :
      E.exposure.defect ≤
        E.exposure.ramification.R *
          E.W.original.aligned.endpoint.defect) :
    AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source := by
  let outer := E.W.original.aligned.toOuterScaleAwareState source
  let a : AdaptiveGeometricRestartState (K := K) :=
    E.exposure.toAdaptiveState E.canonicalSpecial
  let hactive :=
    exists_kernelDependentSupport_of_hessianDefect
      (K := K) (3 : Fin 4) a.family a.defect a.hessianDefect
  let R :=
    kernelSlopeDenominatorClearingRamification
      (3 : Fin 4) a.family
  let q := saturatedKernelSlope (3 : Fin 4) a.family hactive

  have hRpos : 0 < R := by
    dsimp [R]
    exact
      kernelSlopeDenominatorClearingRamification_pos
        (3 : Fin 4) a.family

  have hqpos : 0 < q := by
    dsimp [q]
    exact
      saturatedKernelSlope_pos
        (3 : Fin 4) a.family hactive E.specialFiber_free_three

  let Pram := parameterRamificationFamily (K := K) R a.family
  let hdiv :=
    saturatedKernelSlope_divisibility_afterRamification
      (K := K) (3 : Fin 4) a.family hactive

  have hdefRam :
      HasPolynomialFamilyHessianDefect
        (K := K) Pram (R * a.defect) := by
    dsimp [Pram]
    exact
      parameterRamificationFamily_hasHessianDefect
        R a.defect a.family a.hessianDefect

  have hcost : 2 * q ≤ R * a.defect := by
    dsimp [q, R, Pram, hdiv] at *
    exact
      two_mul_slope_le_of_integralKernelBlowup
        (K := K)
        (3 : Fin 4)
        (saturatedKernelSlope (3 : Fin 4) a.family hactive)
        (kernelSlopeDenominatorClearingRamification
          (3 : Fin 4) a.family * a.defect)
        (parameterRamificationFamily (K := K)
          (kernelSlopeDenominatorClearingRamification
            (3 : Fin 4) a.family) a.family)
        (saturatedKernelSlope_divisibility_afterRamification
          (K := K) (3 : Fin 4) a.family hactive)
        hdefRam

  rcases a.degreeTwoSaturatedKernelStage
      hactive E.specialFiber_free_three with
    ⟨localTarget, hlocalRaw, _hlocalScale, _hlocalSlope, _hactiveTarget⟩

  have hcostPos : 0 < 2 * q := by
    omega
  have hbasePos : 0 < R * a.defect :=
    lt_of_lt_of_le hcostPos hcost
  have hsub : R * a.defect - 2 * q < R * a.defect :=
    Nat.sub_lt hbasePos hcostPos
  have hlocalLt : localTarget.rawDefect < R * a.defect := by
    rw [hlocalRaw]
    simpa [R, q] using hsub

  let target : ScaleAwareAdaptiveGeometricRestartState (K := K) :=
    { localTarget with
      scale :=
        (R * E.exposure.ramification.R) * outer.scale
      scale_pos :=
        Nat.mul_pos
          (Nat.mul_pos hRpos E.exposure.ramification.R_pos)
          outer.scale_pos }

  have hbound :
      R * a.defect ≤
        R * (E.exposure.ramification.R * outer.rawDefect) := by
    apply Nat.mul_le_mul_left R
    simpa [a, outer] using hle

  have hraw :
      target.rawDefect <
        (R * E.exposure.ramification.R) * outer.rawDefect := by
    calc
      target.rawDefect = localTarget.rawDefect := by rfl
      _ < R * a.defect := hlocalLt
      _ ≤ R * (E.exposure.ramification.R * outer.rawDefect) := hbound
      _ = (R * E.exposure.ramification.R) * outer.rawDefect := by
        ac_rfl

  have hspendOuter :
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target outer := by
    change Nonempty (CertifiedRamifiedRawDefectSpend target outer)
    exact
      ⟨{
        ramification := R * E.exposure.ramification.R
        ramification_pos :=
          Nat.mul_pos hRpos E.exposure.ramification.R_pos
        scale_eq := by rfl
        raw_lt := hraw
      }⟩

  have hsource : HasCertifiedRamifiedEpisodeInternalMove outer source := by
    exact
      ⟨E.W.original.aligned.certifiedOuterInternal_of_defect_eq
        source clock_eq⟩

  have hspendSource := hsource.then_spend hspendOuter
  exact hspendSource.toGlobalStrictMacro RR

/-! ## Global frontier after consuming the safe side of the exposure clock -/

/-- The only surviving exposure-clock obstructions after A18.4.11.

`boundaryNondecreasing` includes the exact-clock boundary case: without a
subsequent strict spend, equality is still only a presentation and must not be
called progress.  `kernelFreeOvershoot` is strictly stronger: equality has
already been consumed by the positive saturated-kernel spend above. -/
inductive AdaptiveAlignedSmithCanonicalGlobalExposureClockReducedOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefectReentry
      (hzero : s.rawDefect = 0)
      (D : Nonempty (AdaptiveAlignedSmithCanonicalGlobalZeroDefectReentryData s))

  | ramifiedStrictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s)

  | pointedRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalPresentationThenPointedProgress
          RR s complexity))

  | boundaryNondecreasing
      (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
        (K := K) s)
      (clock_eq :
        E.W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (hclock :
        E.exposure.ramification.R *
            E.W.original.aligned.endpoint.defect ≤
          E.exposure.defect)

  | kernelFreeOvershoot
      (E : AdaptiveAlignedSmithCanonicalGlobalKernelFreeExposureEndpoint
        (K := K) s)
      (clock_eq :
        E.W.original.aligned.endpoint.defect =
          alignedSmithRamificationIndex * s.rawDefect)
      (hclock :
        E.exposure.ramification.R *
            E.W.original.aligned.endpoint.defect <
          E.exposure.defect)

  | blockedPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (trace :
        AdaptiveAlignedSmithCanonicalBlockedPresentationTrace RR s target)

/-- **A18.4.11 exposure-clock reduction.**

Every exposure lying on the safe side of the pure-ramification clock is
consumed immediately.  A lowering boundary is strict on its actual sheared
family; a non-increasing kernel-free exposure becomes strict after the
positive saturated `x₃` contact.  Consequently only a nondecreasing boundary
or a strict kernel-free clock overshoot can remain. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalGlobalExposureClockReducedFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalExposureClockReducedOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalGlobalSurvivingGeometryReducedFrontier
      RR complexity hsrepair with
  | zeroDefectReentry hzero D =>
      exact .zeroDefectReentry hzero D

  | ramifiedStrictMacro D =>
      exact .ramifiedStrictMacro D

  | pointedRankTwoProgress D =>
      exact .pointedRankTwoProgress D

  | exposureBoundary E clock_eq =>
      by_cases hlt :
          E.exposure.defect <
            E.exposure.ramification.R *
              E.W.original.aligned.endpoint.defect
      · exact .ramifiedStrictMacro
          (E.globalRamifiedStrictMacro_of_exposureDefect_lt
            RR clock_eq hlt)
      · exact .boundaryNondecreasing E clock_eq (by omega)

  | kernelFreeExposure E clock_eq =>
      by_cases hle :
          E.exposure.defect ≤
            E.exposure.ramification.R *
              E.W.original.aligned.endpoint.defect
      · exact .ramifiedStrictMacro
          (E.globalRamifiedStrictMacro_of_exposureDefect_le
            RR clock_eq hle)
      · exact .kernelFreeOvershoot E clock_eq (by omega)

  | blockedPresentation target trace =>
      exact .blockedPresentation target trace

end

end HC4.Valuation
