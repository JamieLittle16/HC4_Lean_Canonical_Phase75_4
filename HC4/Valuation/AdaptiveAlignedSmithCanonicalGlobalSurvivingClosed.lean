import HC4.Valuation.AdaptiveAlignedSmithCanonicalSurvivingRigidGeometricTightening
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalCanonicalExposureNeutrality
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalSurvivingExactClockReduction
import Mathlib.Tactic

/-!
# A18.4.27: close the surviving exact-clock geometry

A18.4.26 removes the last geometry-erasing repair branch from the rigid
surviving packet.  This file now consumes an entire `survivingExactClock`
endpoint at its honest absolute scales.

Degree-two saturation is strict because the canonical exposure clock is
exactly neutral and the subsequent saturated kernel contact is positive.
Every marked-point departure is an exact pure presentation.  In the rigid
branch, a preterminal zero-Schur event promotes repair only on the *actual
exposed family* and stores the complete A18.4.26 witness beside that target.
A canonical rigid closing is coordinate-3-free and is therefore strict by the
same saturated-kernel theorem.

Thus the surviving endpoint has no local geometric residue: only zero defect,
a genuine strict macro, a geometry-qualified rank-two successor, or one exact
boundary presentation remains.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## The canonical exposure as an honest absolute-scale presentation -/

namespace AdaptiveAlignedSmithCanonicalSurvivingRigidRankTwoGeometry

/-- Record the canonical exposure family at the actual absolute scale obtained
by composing its ramification with the aligned outer scale. -/
noncomputable def exposedAbsoluteState
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W}
    {R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P}
    {hD : 3 ≤ P.degree}
    (G : AdaptiveAlignedSmithCanonicalSurvivingRigidRankTwoGeometry
      s W P R hD) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) :=
  let outer := W.original.aligned.toOuterScaleAwareState s
  (G.exposure.toAdaptiveState G.canonicalSpecial).toScaleAwareAt
    (G.exposure.ramification.R * outer.scale)
    (Nat.mul_pos G.exposure.ramification.R_pos outer.scale_pos)

/-- The canonical exposure is itself a pure ramified presentation from the
honest aligned outer state. -/
theorem exposedInternalMove_from_outer
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W}
    {R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P}
    {hD : 3 ≤ P.degree}
    (G : AdaptiveAlignedSmithCanonicalSurvivingRigidRankTwoGeometry
      s W P R hD) :
    HasCertifiedRamifiedEpisodeInternalMove
      G.exposedAbsoluteState
      (W.original.aligned.toOuterScaleAwareState s) := by
  let outer := W.original.aligned.toOuterScaleAwareState s
  change Nonempty
    (CertifiedRamifiedEpisodeInternalMove G.exposedAbsoluteState outer)
  refine ⟨{
    ramification := G.exposure.ramification.R
    ramification_pos := G.exposure.ramification.R_pos
    scale_eq := by rfl
    raw_eq := ?_
    degreeCap_eq := by rfl
    sourceComplexity_eq := by rfl
    repair_eq := by rfl
  }⟩
  change G.exposure.defect =
    G.exposure.ramification.R * W.original.aligned.endpoint.defect
  exact G.exposure.canonical_defect_eq_ramified_aligned W

/-- Prefix the canonical exposure by the exact aligned presentation. -/
theorem exposedInternalMove_from_source
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W}
    {R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P}
    {hD : 3 ≤ P.degree}
    (G : AdaptiveAlignedSmithCanonicalSurvivingRigidRankTwoGeometry
      s W P R hD)
    (clock_eq :
      W.original.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect) :
    HasCertifiedRamifiedEpisodeInternalMove G.exposedAbsoluteState s := by
  let outer := W.original.aligned.toOuterScaleAwareState s
  have houter : HasCertifiedRamifiedEpisodeInternalMove outer s :=
    ⟨W.original.aligned.certifiedOuterInternal_of_defect_eq s clock_eq⟩
  have hexposure :
      HasCertifiedRamifiedEpisodeInternalMove G.exposedAbsoluteState outer := by
    simpa [outer] using G.exposedInternalMove_from_outer
  exact houter.trans hexposure

end AdaptiveAlignedSmithCanonicalSurvivingRigidRankTwoGeometry

/-! ## Geometry-qualified rank-two progress on the actual exposure -/

/-- A rigid-surviving rank-two promotion attached to the exact exposed family
which produced the preterminal mixed Schur coefficient. -/
structure AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidRankTwoProgress
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Type (u + 1) where
  W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s
  P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W
  hD : 3 ≤ P.degree
  R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P
  geometry :
    AdaptiveAlignedSmithCanonicalSurvivingRigidRankTwoGeometry s W P R hD
  presented : ScaleAwareAdaptiveGeometricRestartState (K := K)
  presented_eq : presented = geometry.exposedAbsoluteState
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_eq :
    target = presented.withRepairOnly (rankTwoRepairState complexity)
  sourcePresentation : HasCertifiedRamifiedEpisodeInternalMove presented s
  presentedProgress : CertifiedSameScaleEpisodeProgress RR target presented
  globalProgress : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target s

/-- Attach rank promotion only after retaining the actual canonical exposure
and its preterminal Schur witness. -/
noncomputable def AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidRankTwoProgress.ofGeometry
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (hD : 3 ≤ P.degree)
    (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity)
    (clock_eq :
      W.original.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (G : AdaptiveAlignedSmithCanonicalSurvivingRigidRankTwoGeometry
      s W P R hD) :
    AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidRankTwoProgress
      RR s complexity := by
  let presented := G.exposedAbsoluteState
  let target := presented.withRepairOnly (rankTwoRepairState complexity)
  have hpresentedRepair :
      presented.repair = rankOneRepairState complexity := by
    simpa [presented,
      AdaptiveAlignedSmithCanonicalSurvivingRigidRankTwoGeometry.exposedAbsoluteState]
      using hsrepair
  have hrepair :
      RepairProgress presented.repair (rankTwoRepairState complexity) := by
    simpa [hpresentedRepair] using rankOne_to_rankTwo_repairProgress complexity
  have hpresentedProgress :
      CertifiedSameScaleEpisodeProgress RR target presented := by
    apply certifiedSameScaleEpisodeProgress_of_repairProgress (K := K) RR
    · rfl
    · rfl
    · simpa [target, ScaleAwareAdaptiveGeometricRestartState.withRepairOnly]
        using hrepair
  have hglobal : AdaptiveAlignedSmithCanonicalGlobalMacroProgress target s := by
    unfold AdaptiveAlignedSmithCanonicalGlobalMacroProgress
    unfold ScaleAwareAdaptiveGeometricRestartState.globalMacroKey
    apply Prod.Lex.left
    simpa [target, presented,
      AdaptiveAlignedSmithCanonicalSurvivingRigidRankTwoGeometry.exposedAbsoluteState,
      ScaleAwareAdaptiveGeometricRestartState.withRepairOnly, hsrepair] using
      repairState_measure_lt_of_progress
        (rankOne_to_rankTwo_repairProgress complexity)
  exact {
    W := W
    P := P
    hD := hD
    R := R
    geometry := G
    presented := presented
    presented_eq := rfl
    target := target
    target_eq := rfl
    sourcePresentation := by
      simpa [presented] using G.exposedInternalMove_from_source clock_eq
    presentedProgress := hpresentedProgress
    globalProgress := hglobal
  }

/-! ## Fully closed surviving endpoint -/

/-- No local surviving geometry remains after A18.4.27.  A boundary remains an
explicit pure presentation and is deliberately not recursive progress. -/
inductive AdaptiveAlignedSmithCanonicalGlobalSurvivingClosedOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefectReentry
      (hzero : s.rawDefect = 0)
      (D : Nonempty (AdaptiveAlignedSmithCanonicalGlobalZeroDefectReentryData s))

  | ramifiedStrictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s)

  | rigidRankTwoProgress
      (D : Nonempty
        (AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidRankTwoProgress
          RR s complexity))

  | exactBoundaryPresentation
      (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
        (K := K) s)
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (target_eq : target = E.toAbsoluteBoundaryState)
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target s)

/-- Package an exposure boundary using the exact canonical exposure clock. -/
private theorem exposureBoundary_to_closed
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
      (K := K) s)
    (clock_eq :
      E.W.original.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect) :
    AdaptiveAlignedSmithCanonicalGlobalSurvivingClosedOutcome
      RR s complexity := by
  let target := E.toAbsoluteBoundaryState
  exact .exactBoundaryPresentation E target rfl
    (by
      simpa [target] using E.certifiedInternalMove_from_source clock_eq)

/-- **A18.4.27 surviving exact-clock closure.** -/
theorem AdaptiveAlignedSmithSurvivingStateEndpoint.globalClosedReduction
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (complexity : ℕ)
    (clock_eq :
      W.original.aligned.endpoint.defect =
        alignedSmithRamificationIndex * s.rawDefect)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalSurvivingClosedOutcome
      RR s complexity := by
  cases W.globalExactClockReduction RR s complexity clock_eq hsrepair with
  | zeroDefectReentry hzero D =>
      exact .zeroDefectReentry hzero D

  | ramifiedStrictMacro D =>
      exact .ramifiedStrictMacro D

  | degreeTwoBoundary W P hD B hclock =>
      let E := B.toGlobalExposureBoundary
      exact exposureBoundary_to_closed RR E hclock

  | degreeTwoSaturated W P hD S hclock =>
      let E := S.toGlobalKernelFreeExposure P
      have hexact := E.exposure.canonical_defect_eq_ramified_aligned E.W
      exact .ramifiedStrictMacro
        (E.globalRamifiedStrictMacro_of_exposureDefect_le RR hclock
          (le_of_eq hexact))

  | rigidPacket W P hD R hclock =>
      cases R.geometricTightOutcome s W P hD with
      | zeroDefect hzero =>
          have hsZero : s.rawDefect = 0 :=
            W.source_rawDefect_eq_zero_of_aligned hclock hzero
          exact .zeroDefectReentry hsZero
            (s.exists_globalZeroDefectReentryData hsZero)

      | exposureBoundary d hboundary =>
          let E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
              (K := K) s := {
            W := W
            exposure := d
            boundary := hboundary
          }
          exact exposureBoundary_to_closed RR E hclock

      | rankTwoGeometry hG =>
          rcases hG with ⟨G⟩
          exact .rigidRankTwoProgress
            ⟨AdaptiveAlignedSmithCanonicalGlobalSurvivingRigidRankTwoProgress.ofGeometry
              RR W P hD R complexity hsrepair hclock G⟩

      | canonicalClosing C hspecial =>
          let E : AdaptiveAlignedSmithCanonicalGlobalKernelFreeExposureEndpoint
              (K := K) s := {
            W := W
            exposure := C.exposure
            canonicalSpecial := hspecial
            specialFiber_free_three := by
              simpa using C.specialFiber_free_three hspecial
          }
          have hexact := E.exposure.canonical_defect_eq_ramified_aligned E.W
          exact .ramifiedStrictMacro
            (E.globalRamifiedStrictMacro_of_exposureDefect_le RR hclock
              (le_of_eq hexact))

end

end HC4.Valuation
