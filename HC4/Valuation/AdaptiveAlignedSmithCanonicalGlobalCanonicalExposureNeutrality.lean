import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalExposureClockReduction
import Mathlib.Tactic

/-!
# A18.4.12: the canonical surviving Smith exposure has neutral clock correction

A18.4.11 deliberately treated a surviving-wall coefficientwise Smith exposure
as a generic realised integral wall.  That was the safe local interface, but
the actual global pipeline is more rigid: every surviving wall comes from the
canonical Smith classifier at

    base = 0,   level = 0.

The corresponding realisation has zero transverse source weight and zero
offset.  Consequently its *combined* source weight is exactly

    [0, 2, 2, 4]

and its combined divided level is exactly `4`.  Therefore the correction in
the exact exposure determinant clock vanishes identically:

    2 * sum W - 4 * m = 16 - 16 = 0.

So every actual surviving-wall exposure in the canonical pipeline satisfies

    exposure.defect = R * aligned.defect.

There is no genuine exposure overshoot branch.  In particular the
`kernelFreeOvershoot` residue of A18.4.11 is impossible, while a boundary on
the nondecreasing side is forced to be an exact ramified internal
presentation.  This module packages that presentation at the honest absolute
scale and removes the exposure-clock arithmetic from the global frontier.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Canonical numerical exposure clock -/

/-- The common divided level of an exposure built from a canonical surviving
wall is exactly `4`. -/
theorem AdaptiveSurvivingWallExposureData.canonical_commonLevel_eq_four
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (d : AdaptiveSurvivingWallExposureData
      (W.original.aligned.toAdaptiveState s) W.wall) :
    d.commonLevel = 4 := by
  have hlevel := W.combinedSourceLevel_eq_four s
  have h := d.commonLevel_eq
  rw [hlevel] at h
  exact_mod_cast h

/-- **Canonical exposure clock identity.**

The coefficientwise exposure attached to the canonical surviving wall is
exactly a pure ramification at the raw Hessian-clock level. -/
theorem AdaptiveSurvivingWallExposureData.canonical_defect_eq_ramified_aligned
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (d : AdaptiveSurvivingWallExposureData
      (W.original.aligned.toAdaptiveState s) W.wall) :
    d.defect =
      d.ramification.R * W.original.aligned.endpoint.defect := by
  have hsum := W.combinedSourceWeight_sum s
  have hm := d.canonical_commonLevel_eq_four W
  unfold AdaptiveSurvivingWallExposureData.defect
  rw [hsum]
  calc
    d.ramification.R *
          (W.original.aligned.toAdaptiveState s).defect +
        2 * 8 - 4 * d.commonLevel =
        d.ramification.R *
          (W.original.aligned.toAdaptiveState s).defect := by
      omega
    _ = d.ramification.R * W.original.aligned.endpoint.defect := by
      simp

/-! ## Exact boundary exposure as an honest absolute-scale presentation -/

/-- Record the canonically normalised boundary family at the absolute scale
obtained by composing the exposure ramification with the aligned outer scale. -/
noncomputable def AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint.toAbsoluteBoundaryState
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
      (K := K) source) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) :=
  let outer := E.W.original.aligned.toOuterScaleAwareState source
  let B : AdaptiveSmithExposureSectionBoundary E.exposure :=
    Classical.choice E.boundary
  B.toAdaptiveState.toScaleAwareAt
    (E.exposure.ramification.R * outer.scale)
    (Nat.mul_pos E.exposure.ramification.R_pos outer.scale_pos)

/-- At the canonical wall, the boundary-normalised exposure is a certified
pure ramified internal move from the honest aligned outer state. -/
theorem AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint.certifiedInternalMove_from_outer
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
      (K := K) source) :
    HasCertifiedRamifiedEpisodeInternalMove
      E.toAbsoluteBoundaryState
      (E.W.original.aligned.toOuterScaleAwareState source) := by
  let outer := E.W.original.aligned.toOuterScaleAwareState source
  let B : AdaptiveSmithExposureSectionBoundary E.exposure :=
    Classical.choice E.boundary
  let target := E.toAbsoluteBoundaryState
  have hrawCanonical :=
    E.exposure.canonical_defect_eq_ramified_aligned E.W
  change Nonempty (CertifiedRamifiedEpisodeInternalMove target outer)
  refine ⟨{
    ramification := E.exposure.ramification.R
    ramification_pos := E.exposure.ramification.R_pos
    scale_eq := by rfl
    raw_eq := ?_
    degreeCap_eq := by rfl
    sourceComplexity_eq := by rfl
    repair_eq := by rfl
  }⟩
  change E.exposure.defect =
    E.exposure.ramification.R * E.W.original.aligned.endpoint.defect
  exact hrawCanonical

/-- Prefix the exact boundary exposure by the already-certified aligned
presentation.  The result is an honest internal presentation from `source`
itself, not recursive progress. -/
theorem AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint.certifiedInternalMove_from_source
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
      (K := K) source)
    (clock_eq :
      E.W.original.aligned.endpoint.defect =
        alignedSmithRamificationIndex * source.rawDefect) :
    HasCertifiedRamifiedEpisodeInternalMove
      E.toAbsoluteBoundaryState source := by
  let outer := E.W.original.aligned.toOuterScaleAwareState source
  have hsource : HasCertifiedRamifiedEpisodeInternalMove outer source := by
    exact
      ⟨E.W.original.aligned.certifiedOuterInternal_of_defect_eq
        source clock_eq⟩
  have hboundary :
      HasCertifiedRamifiedEpisodeInternalMove
        E.toAbsoluteBoundaryState outer := by
    simpa [outer] using E.certifiedInternalMove_from_outer
  exact hsource.trans hboundary

/-! ## Global exposure-neutral frontier -/

/-- After restoring canonical-wall provenance there is no exposure overshoot.
The only non-strict exposure residue is a genuine exact boundary
presentation, already equipped with its certified absolute-scale internal
move. -/
inductive AdaptiveAlignedSmithCanonicalGlobalCanonicalExposureOutcome
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

  | exactBoundaryPresentation
      (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
        (K := K) s)
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (target_eq : target = E.toAbsoluteBoundaryState)
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)

  | blockedPresentation
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (trace :
        AdaptiveAlignedSmithCanonicalBlockedPresentationTrace RR s target)

/-- **A18.4.12 canonical exposure neutrality.**

The `kernelFreeOvershoot` branch of A18.4.11 is contradictory.  A
nondecreasing exposure boundary is forced onto the exact pure-ramification
clock and is returned as a certified internal presentation at its real
absolute scale. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalGlobalCanonicalExposureFrontier
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalCanonicalExposureOutcome
      RR s complexity := by
  cases s.alignedSmithCanonicalGlobalExposureClockReducedFrontier
      RR complexity hsrepair with
  | zeroDefectReentry hzero D =>
      exact .zeroDefectReentry hzero D

  | ramifiedStrictMacro D =>
      exact .ramifiedStrictMacro D

  | pointedRankTwoProgress D =>
      exact .pointedRankTwoProgress D

  | boundaryNondecreasing E clock_eq hclock =>
      have hexact :=
        E.exposure.canonical_defect_eq_ramified_aligned E.W
      have heq :
          E.exposure.defect =
            E.exposure.ramification.R *
              E.W.original.aligned.endpoint.defect := hexact
      let target := E.toAbsoluteBoundaryState
      have hmove : HasCertifiedRamifiedEpisodeInternalMove target s := by
        dsimp [target]
        exact E.certifiedInternalMove_from_source clock_eq
      exact .exactBoundaryPresentation E target rfl hmove

  | kernelFreeOvershoot E clock_eq hclock =>
      have hexact :=
        E.exposure.canonical_defect_eq_ramified_aligned E.W
      omega

  | blockedPresentation target trace =>
      exact .blockedPresentation target trace

end

end HC4.Valuation
