import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwo
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalCanonicalExposureNeutrality
import HC4.Valuation.AdaptiveAlignedSmithCanonicalDirectResidualClosure
import Mathlib.Tactic

/-!
# A18.4.27: consume the surviving-wall exact-clock residue

A18.4.25 leaves `survivingExactClock` as one of only two non-exit constructors.
The older A18.4.8 surviving-wall reduction is sound through its three concrete
packet residues, but the historical rigid-packet consumer later forgot that a
rank-two zero-Schur witness lived on the Smith-exposure family.  A18.4.26 fixes
exactly that branch.

This file now closes the complete surviving wall without using the old
geometry-erasing rigid dispatcher.

* degree-two boundary gives the already-proved exact canonical exposure
  presentation;
* degree-two saturation gives a strict kernel-free spend, because the
  canonical exposure clock is exactly neutral;
* the direct degree-at-least-three rank-two family continuation is the existing
  honest absolute-scale macro;
* a rigid packet is split by A18.4.26 into zero defect, a genuine boundary,
  canonical zero-Schur closing, or rank-two geometry on the actual exposure;
* canonical zero-Schur closing is kernel-free and therefore strict;
* canonical exposure rank-two geometry is first certified as a pure exposure
  presentation and only then promoted on that same exposed family.

Thus `survivingExactClock` disappears completely.  The sole non-strict output
of a surviving wall is an exact boundary presentation, which remains
bookkeeping rather than recursive progress.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Canonical exposure itself is an honest internal presentation -/

/-- If a canonical surviving-wall exposure keeps its marked point at `e₀`,
recording it at the true absolute exposure scale gives a certified pure
ramified internal move from the aligned outer state. -/
theorem AdaptiveSurvivingWallExposureData.certifiedCanonicalInternalMove_from_outer
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (d : AdaptiveSurvivingWallExposureData
      (W.original.aligned.toAdaptiveState s) W.wall)
    (hspecial :
      polynomialSectionSpecialPoint d.rightSection =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    let outer := W.original.aligned.toOuterScaleAwareState s
    let target :=
      (d.toAdaptiveState hspecial).toScaleAwareAt
        (d.ramification.R * outer.scale)
        (Nat.mul_pos d.ramification.R_pos outer.scale_pos)
    HasCertifiedRamifiedEpisodeInternalMove target outer := by
  dsimp only
  let outer := W.original.aligned.toOuterScaleAwareState s
  let target :=
    (d.toAdaptiveState hspecial).toScaleAwareAt
      (d.ramification.R * outer.scale)
      (Nat.mul_pos d.ramification.R_pos outer.scale_pos)
  have hraw := d.canonical_defect_eq_ramified_aligned W
  change Nonempty (CertifiedRamifiedEpisodeInternalMove target outer)
  exact ⟨{
    ramification := d.ramification.R
    ramification_pos := d.ramification.R_pos
    scale_eq := by rfl
    raw_eq := by
      change d.defect = d.ramification.R * W.original.aligned.endpoint.defect
      exact hraw
    degreeCap_eq := by rfl
    sourceComplexity_eq := by rfl
    repair_eq := by rfl
  }⟩

/-- The A18.4.26 rank-two target is therefore a standard honest ramified
strict macro: source -> aligned outer -> canonical exposure -> rank-two target. -/
theorem AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress.toRamifiedStrictMacro
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W}
    {R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P}
    {hD : 3 ≤ P.degree}
    {complexity : ℕ}
    (D : AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress
      RR s W P R hD complexity) :
    AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s := by
  have hexposure0 :=
    D.geometry.exposure.certifiedCanonicalInternalMove_from_outer
      W D.geometry.canonicalSpecial
  have hexposure : HasCertifiedRamifiedEpisodeInternalMove D.exposed D.outer := by
    rw [D.exposed_eq, D.outer_eq]
    simpa using hexposure0
  have hsource : HasCertifiedRamifiedEpisodeInternalMove D.exposed s :=
    D.alignedPresentation.trans hexposure
  exact .mk D.exposed D.target hsource D.exposedProgress

/-! ## One surviving exact-clock leaf -/

/-- Sound final outcome of one surviving exact-clock leaf. -/
inductive AdaptiveAlignedSmithCanonicalGlobalSoundSurvivingExactClockOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefectReentry
      (hzero : s.rawDefect = 0)
      (D : Nonempty (AdaptiveAlignedSmithCanonicalGlobalZeroDefectReentryData s))

  | ramifiedStrictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s)

  | exactBoundaryPresentation
      (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
        (K := K) s)
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (target_eq : target = E.toAbsoluteBoundaryState)
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)

/-- **A18.4.27 surviving-wall closure.**

This reuses the sound A18.4.8 packet split but replaces only its rigid residue
with the geometry-preserving A18.4.26 theorem. -/
theorem AdaptiveAlignedSmithSurvivingStateEndpoint.soundGlobalExactClockReduction
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (complexity : ℕ)
    (clock_eq :
      W.original.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalSoundSurvivingExactClockOutcome
      RR s complexity := by
  cases W.globalExactClockReduction RR s complexity clock_eq hsrepair with
  | zeroDefectReentry hzero D =>
      exact .zeroDefectReentry hzero D

  | ramifiedStrictMacro D =>
      exact .ramifiedStrictMacro D

  | degreeTwoBoundary W' P hD B hclock =>
      let E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
          (K := K) s := B.toGlobalExposureBoundary
      let target := E.toAbsoluteBoundaryState
      have hmove : HasCertifiedRamifiedEpisodeInternalMove target s := by
        dsimp [target]
        exact E.certifiedInternalMove_from_source hclock
      exact .exactBoundaryPresentation E target rfl hmove

  | degreeTwoSaturated W' P hD S hclock =>
      let E : AdaptiveAlignedSmithCanonicalGlobalKernelFreeExposureEndpoint
          (K := K) s := S.toGlobalKernelFreeExposure P
      have hexact := E.exposure.canonical_defect_eq_ramified_aligned E.W
      have hle :
          E.exposure.defect ≤
            E.exposure.ramification.R *
              E.W.original.aligned.endpoint.defect := by
        omega
      exact .ramifiedStrictMacro
        (E.globalRamifiedStrictMacro_of_exposureDefect_le RR hclock hle)

  | rigidPacket W' P hD R hclock =>
      cases R.geometricExposureOutcome s W' P hD complexity with
      | zeroDefect hzero =>
          have hsZero : s.rawDefect = 0 :=
            W'.source_rawDefect_eq_zero_of_aligned hclock hzero
          exact .zeroDefectReentry hsZero
            (s.exists_globalZeroDefectReentryData hsZero)

      | boundary exposure hboundary =>
          let E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
              (K := K) s := {
            W := W'
            exposure := exposure
            boundary := hboundary
          }
          let target := E.toAbsoluteBoundaryState
          have hmove : HasCertifiedRamifiedEpisodeInternalMove target s := by
            dsimp [target]
            exact E.certifiedInternalMove_from_source hclock
          exact .exactBoundaryPresentation E target rfl hmove

      | rankTwoGeometry hgeometry =>
          rcases hgeometry with ⟨G⟩
          let D :=
            AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidExposureRankTwoProgress.ofGeometry
              RR W' P R hD complexity hsrepair G
          exact .ramifiedStrictMacro D.toRamifiedStrictMacro

      | canonicalClosing C hspecial =>
          let E : AdaptiveAlignedSmithCanonicalGlobalKernelFreeExposureEndpoint
              (K := K) s := {
            W := W'
            exposure := C.exposure
            canonicalSpecial := hspecial
            specialFiber_free_three := C.specialFiber_free_three hspecial
          }
          have hexact := E.exposure.canonical_defect_eq_ramified_aligned E.W
          have hle :
              E.exposure.defect ≤
                E.exposure.ramification.R *
                  E.W.original.aligned.endpoint.defect := by
            omega
          exact .ramifiedStrictMacro
            (E.globalRamifiedStrictMacro_of_exposureDefect_le RR hclock hle)

/-! ## Splice into the geometry-preserving exact-clock frontier -/

/-- Exact-clock frontier after `survivingExactClock` has been completely
consumed.  The only non-exit constructor left is a boundary presentation. -/
inductive AdaptiveAlignedSmithCanonicalExactClockSurvivingClosedOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefect (hzero : s.rawDefect = 0)

  | ramifiedSpend
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (h : AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s)

  | stationaryRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalStationaryRankTwoProgress
          RR s complexity))

  | earlySchurRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalEarlySchurRankTwoProgress
          RR s complexity))

  | residualRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalResidualRankTwoProgress
          RR s complexity))

  | zeroSchurRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalZeroSchurRankTwoProgress
          RR s complexity))

  | ramifiedStrictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s)

  | exposureBoundaryPresentation
      (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
        (K := K) s)
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (target_eq : target = E.toAbsoluteBoundaryState)
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)

  | sectionBoundaryInternal
      (B : AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) s.degreeCap s.rawDefect
        (zeroJetNormalizedFamily s.family) s.movingSection)

/-- **A18.4.27 global splice.**  No surviving-wall packet remains. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalExactClockSurvivingClosedFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalExactClockSurvivingClosedOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalExactClockDirectClosedFrontier
      RR complexity hsrepair with
  | zeroDefect hzero => exact .zeroDefect hzero
  | ramifiedSpend target h => exact .ramifiedSpend target h
  | stationaryRankTwoProgress D => exact .stationaryRankTwoProgress D
  | earlySchurRankTwoProgress D => exact .earlySchurRankTwoProgress D
  | residualRankTwoProgress D => exact .residualRankTwoProgress D
  | zeroSchurRankTwoProgress D => exact .zeroSchurRankTwoProgress D
  | sectionBoundaryInternal B => exact .sectionBoundaryInternal B
  | survivingExactClock W clock_eq =>
      cases W.soundGlobalExactClockReduction
          RR s complexity clock_eq hsrepair with
      | zeroDefectReentry hzero D => exact .zeroDefect hzero
      | ramifiedStrictMacro D => exact .ramifiedStrictMacro D
      | exactBoundaryPresentation E target target_eq hmove =>
          exact .exposureBoundaryPresentation E target target_eq hmove

end

end HC4.Valuation
