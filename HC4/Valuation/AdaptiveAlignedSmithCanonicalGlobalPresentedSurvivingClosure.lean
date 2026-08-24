import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentedEndpointScaleBridge
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalSurvivingWallClosure
import Mathlib.Tactic

/-!
# A18.4.31: close a presented surviving endpoint at its current scale

A18.4.30 identifies the ordinary adaptive state carried by a presented
surviving endpoint with the actual stored scale-aware state.  We can therefore
consume the entire surviving-wall packet without re-running aligned Smith and
without introducing another factor `20`.

The local split is the same geometry already used by A18.4.27:

* zero determinant clock reflects through the stored source presentation;
* a genuine rank-two packet lifts at the current absolute scale;
* degree-two saturation and canonical rigid closing use the positive
  kernel-free exposure restart;
* a marked-point exposure boundary remains only an honest pure presentation;
* rigid zero-Schur rank-two geometry promotes the actual exposed family, not
  the pre-exposure family.

Thus a presented surviving endpoint has only three global outcomes: source
zero defect, genuine strict macro, or one exact exposure-boundary
presentation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Exposure helpers based at the current presented state -/

/-- A canonical surviving exposure, recorded directly over an already
presented endpoint, is a pure ramified presentation at the current absolute
scale. -/
theorem AdaptiveSurvivingWallExposureData.certifiedInternalMove_from_presented
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (d : AdaptiveSurvivingWallExposureData
      (W.original.aligned.toAdaptiveState s) W.wall)
    (hspecial :
      polynomialSectionSpecialPoint d.rightSection =
        coordinateAxisPoint (K := K) (0 : Fin 4))
    (hclock : W.original.aligned.endpoint.defect = s.rawDefect) :
    let target :=
      (d.toAdaptiveState hspecial).toScaleAwareAt
        (d.ramification.R * s.scale)
        (Nat.mul_pos d.ramification.R_pos s.scale_pos)
    HasCertifiedRamifiedEpisodeInternalMove target s := by
  dsimp only
  let target :=
    (d.toAdaptiveState hspecial).toScaleAwareAt
      (d.ramification.R * s.scale)
      (Nat.mul_pos d.ramification.R_pos s.scale_pos)
  have hraw := d.canonical_defect_eq_ramified_aligned W
  change Nonempty (CertifiedRamifiedEpisodeInternalMove target s)
  exact ⟨{
    ramification := d.ramification.R
    ramification_pos := d.ramification.R_pos
    scale_eq := by rfl
    raw_eq := by
      change d.defect = d.ramification.R * s.rawDefect
      rw [hraw, hclock]
    degreeCap_eq := by rfl
    sourceComplexity_eq := by rfl
    repair_eq := by rfl
  }⟩

/-- Boundary-normalised form of a canonical exposure, but based on the
endpoint's current absolute scale rather than the historical aligned outer
scale. -/
noncomputable def AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint.toPresentedBoundaryState
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
      (K := K) s) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) :=
  let B : AdaptiveSmithExposureSectionBoundary E.exposure :=
    Classical.choice E.boundary
  B.toAdaptiveState.toScaleAwareAt
    (E.exposure.ramification.R * s.scale)
    (Nat.mul_pos E.exposure.ramification.R_pos s.scale_pos)

/-- If the canonical endpoint clock already equals the presented state's raw
clock, an exposure boundary is an exact pure presentation from that state. -/
theorem AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint.certifiedInternalMove_from_presented
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
      (K := K) s)
    (hclock : E.W.original.aligned.endpoint.defect = s.rawDefect) :
    HasCertifiedRamifiedEpisodeInternalMove
      E.toPresentedBoundaryState s := by
  let B : AdaptiveSmithExposureSectionBoundary E.exposure :=
    Classical.choice E.boundary
  let target := E.toPresentedBoundaryState
  have hraw := E.exposure.canonical_defect_eq_ramified_aligned E.W
  change Nonempty (CertifiedRamifiedEpisodeInternalMove target s)
  exact ⟨{
    ramification := E.exposure.ramification.R
    ramification_pos := E.exposure.ramification.R_pos
    scale_eq := by rfl
    raw_eq := by
      change E.exposure.defect = E.exposure.ramification.R * s.rawDefect
      rw [hraw, hclock]
    degreeCap_eq := by rfl
    sourceComplexity_eq := by rfl
    repair_eq := by rfl
  }⟩

/-- Kernel-free canonical exposure is strictly consumable from an already
presented endpoint.  This is A18.4.11's positive first-contact argument with
its absolute scale based directly at `s.scale`, not at `20 * s.scale`. -/
theorem AdaptiveAlignedSmithCanonicalGlobalKernelFreeExposureEndpoint.globalRamifiedStrictMacro_from_presented
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    (E : AdaptiveAlignedSmithCanonicalGlobalKernelFreeExposureEndpoint
      (K := K) D.presented)
    (hclock : E.W.original.aligned.endpoint.defect = D.presented.rawDefect) :
    AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source := by
  let s := D.presented
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
    exact kernelSlopeDenominatorClearingRamification_pos
      (3 : Fin 4) a.family

  have hqpos : 0 < q := by
    dsimp [q]
    exact saturatedKernelSlope_pos
      (3 : Fin 4) a.family hactive E.specialFiber_free_three

  let Pram := parameterRamificationFamily (K := K) R a.family
  let hdiv :=
    saturatedKernelSlope_divisibility_afterRamification
      (K := K) (3 : Fin 4) a.family hactive

  have hdefRam :
      HasPolynomialFamilyHessianDefect
        (K := K) Pram (R * a.defect) := by
    dsimp [Pram]
    exact parameterRamificationFamily_hasHessianDefect
      R a.defect a.family a.hessianDefect

  have hcost : 2 * q ≤ R * a.defect := by
    dsimp [q, R, Pram, hdiv] at *
    exact two_mul_slope_le_of_integralKernelBlowup
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

  have hcostPos : 0 < 2 * q := by omega
  have hbasePos : 0 < R * a.defect :=
    lt_of_lt_of_le hcostPos hcost
  have hsub : R * a.defect - 2 * q < R * a.defect :=
    Nat.sub_lt hbasePos hcostPos
  have hlocalLt : localTarget.rawDefect < R * a.defect := by
    rw [hlocalRaw]
    simpa [R, q] using hsub

  let target : ScaleAwareAdaptiveGeometricRestartState (K := K) :=
    { localTarget with
      scale := (R * E.exposure.ramification.R) * s.scale
      scale_pos :=
        Nat.mul_pos
          (Nat.mul_pos hRpos E.exposure.ramification.R_pos)
          s.scale_pos }

  have hexact := E.exposure.canonical_defect_eq_ramified_aligned E.W
  have haDef :
      a.defect = E.exposure.ramification.R * s.rawDefect := by
    simpa [a] using (hexact.trans (congrArg (fun n => E.exposure.ramification.R * n) hclock))

  have hraw :
      target.rawDefect <
        (R * E.exposure.ramification.R) * s.rawDefect := by
    calc
      target.rawDefect = localTarget.rawDefect := by rfl
      _ < R * a.defect := hlocalLt
      _ = R * (E.exposure.ramification.R * s.rawDefect) := by rw [haDef]
      _ = (R * E.exposure.ramification.R) * s.rawDefect := by ac_rfl

  have hspend :
      AdaptiveAlignedSmithBlockerClockProvenance.HasCertifiedRamifiedRawDefectSpend
        target s := by
    change Nonempty (CertifiedRamifiedRawDefectSpend target s)
    exact ⟨{
      ramification := R * E.exposure.ramification.R
      ramification_pos := Nat.mul_pos hRpos E.exposure.ramification.R_pos
      scale_eq := by rfl
      raw_lt := hraw
    }⟩

  exact (hspend.toGlobalStrictMacro RR).prepend_internal RR D.sourcePresentation

/-! ## Rigid zero-Schur rank promotion on the exposed family -/

/-- Geometry retained by A18.4.26 promotes rank two on the literal exposed
family at the current presented scale. -/
theorem AdaptiveAlignedSmithCanonicalSurvivingRigidExposureRankTwoGeometry.globalRamifiedStrictMacro_from_presented
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint
      (K := K) D.presented D.toStateEndpoint}
    {R : AdaptiveAlignedSmithRigidPacketEndpoint
      (K := K) D.presented D.toStateEndpoint P}
    {hD : 3 ≤ P.degree}
    {complexity : ℕ}
    (G : AdaptiveAlignedSmithCanonicalSurvivingRigidExposureRankTwoGeometry
      D.toStateEndpoint P R hD complexity)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source := by
  let s := D.presented
  let exposed :=
    (G.exposure.toAdaptiveState G.canonicalSpecial).toScaleAwareAt
      (G.exposure.ramification.R * s.scale)
      (Nat.mul_pos G.exposure.ramification.R_pos s.scale_pos)
  let target := exposed.withRepairOnly (rankTwoRepairState complexity)

  have hclock :
      D.toStateEndpoint.original.aligned.endpoint.defect = s.rawDefect := by
    simpa [s, AdaptiveAlignedSmithCanonicalPresentedSurviving.toStateEndpoint]
      using D.defect_eq

  have hexposed : HasCertifiedRamifiedEpisodeInternalMove exposed s := by
    simpa [exposed] using
      G.exposure.certifiedInternalMove_from_presented
        D.toStateEndpoint G.canonicalSpecial hclock

  have hsrepairPresented : s.repair = rankOneRepairState complexity := by
    rcases D.sourcePresentation with ⟨hmove⟩
    dsimp [s]
    rw [hmove.repair_eq]
    exact hsrepair

  have hexposedRepair : exposed.repair = rankOneRepairState complexity := by
    change s.repair = rankOneRepairState complexity
    exact hsrepairPresented

  have hrepair :
      RepairProgress exposed.repair (rankTwoRepairState complexity) := by
    simpa [hexposedRepair] using G.repairProgress

  have hprogress : CertifiedSameScaleEpisodeProgress RR target exposed := by
    apply certifiedSameScaleEpisodeProgress_of_repairProgress (K := K) RR
    · rfl
    · rfl
    · simpa [target, ScaleAwareAdaptiveGeometricRestartState.withRepairOnly]
        using hrepair

  let local : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR s :=
    .mk exposed target hexposed hprogress
  exact local.prepend_internal RR D.sourcePresentation

/-! ## Complete presented-surviving closure -/

inductive AdaptiveAlignedSmithCanonicalPresentedSurvivingClosureOutcome
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | zeroDefect
      (hzero : source.rawDefect = 0)

  | ramifiedStrictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source)

  | exposureBoundaryPresentation
      (presented : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
        (K := K) presented)
      (target : ScaleAwareAdaptiveGeometricRestartState (K := K))
      (target_eq : target = E.toPresentedBoundaryState)
      (hmove : HasCertifiedRamifiedEpisodeInternalMove target source)

/-- **A18.4.31 presented surviving closure.** -/
theorem AdaptiveAlignedSmithCanonicalPresentedSurviving.soundReduction
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    (complexity : ℕ)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalPresentedSurvivingClosureOutcome
      RR source complexity := by
  let s := D.presented
  let W := D.toStateEndpoint
  rcases W.persistentPacket s with ⟨P⟩
  rcases P.degree_eq_two_or_three_le s W with hD2 | hD3

  · rcases P.degreeTwo_zeroDefect_or_boundary_or_saturated
        s W hD2 with hzero | hboundary | hsaturated

    · have hsZero : s.rawDefect = 0 := by
        change W.original.aligned.endpoint.defect = 0 at hzero
        have hclock : W.original.aligned.endpoint.defect = s.rawDefect := by
          simpa [s, W,
            AdaptiveAlignedSmithCanonicalPresentedSurviving.toStateEndpoint]
            using D.defect_eq
        rw [hclock] at hzero
        exact hzero
      exact .zeroDefect
        (D.sourcePresentation.source_rawDefect_eq_zero_of_target hsZero)

    · rcases hboundary with ⟨B⟩
      let E := B.toGlobalExposureBoundary
      have hclock : E.W.original.aligned.endpoint.defect = s.rawDefect := by
        simpa [E, s, W,
          AdaptiveAlignedSmithCanonicalPresentedSurviving.toStateEndpoint]
          using D.defect_eq
      let target := E.toPresentedBoundaryState
      have hpresented : HasCertifiedRamifiedEpisodeInternalMove target s := by
        dsimp [target]
        exact E.certifiedInternalMove_from_presented hclock
      exact .exposureBoundaryPresentation s E target rfl
        (D.sourcePresentation.trans hpresented)

    · rcases hsaturated with ⟨S⟩
      let E := S.toGlobalKernelFreeExposure P
      have hclock : E.W.original.aligned.endpoint.defect = s.rawDefect := by
        simpa [E, s, W,
          AdaptiveAlignedSmithCanonicalPresentedSurviving.toStateEndpoint]
          using D.defect_eq
      exact .ramifiedStrictMacro
        (E.globalRamifiedStrictMacro_from_presented RR D hclock)

  · rcases P.rigid_or_rankTwoFamilyContinuation s W complexity with
      hrigid | hrankTwo

    · rcases hrigid with ⟨R⟩
      cases R.geometricExposureOutcome s W P hD3 complexity with
      | zeroDefect hzero =>
          have hsZero : s.rawDefect = 0 := by
            change W.original.aligned.endpoint.defect = 0 at hzero
            have hclock : W.original.aligned.endpoint.defect = s.rawDefect := by
              simpa [s, W,
                AdaptiveAlignedSmithCanonicalPresentedSurviving.toStateEndpoint]
                using D.defect_eq
            rw [hclock] at hzero
            exact hzero
          exact .zeroDefect
            (D.sourcePresentation.source_rawDefect_eq_zero_of_target hsZero)

      | boundary exposure hboundary =>
          let E : AdaptiveAlignedSmithCanonicalGlobalExposureBoundaryEndpoint
              (K := K) s := {
            W := W
            exposure := exposure
            boundary := hboundary
          }
          have hclock : E.W.original.aligned.endpoint.defect = s.rawDefect := by
            simpa [E, s, W,
              AdaptiveAlignedSmithCanonicalPresentedSurviving.toStateEndpoint]
              using D.defect_eq
          let target := E.toPresentedBoundaryState
          have hpresented : HasCertifiedRamifiedEpisodeInternalMove target s := by
            dsimp [target]
            exact E.certifiedInternalMove_from_presented hclock
          exact .exposureBoundaryPresentation s E target rfl
            (D.sourcePresentation.trans hpresented)

      | rankTwoGeometry hgeometry =>
          rcases hgeometry with ⟨G⟩
          exact .ramifiedStrictMacro
            (G.globalRamifiedStrictMacro_from_presented RR D hsrepair)

      | canonicalClosing C hspecial =>
          let E : AdaptiveAlignedSmithCanonicalGlobalKernelFreeExposureEndpoint
              (K := K) s := {
            W := W
            exposure := C.exposure
            canonicalSpecial := hspecial
            specialFiber_free_three := C.specialFiber_free_three hspecial
          }
          have hclock : E.W.original.aligned.endpoint.defect = s.rawDefect := by
            simpa [E, s, W,
              AdaptiveAlignedSmithCanonicalPresentedSurviving.toStateEndpoint]
              using D.defect_eq
          exact .ramifiedStrictMacro
            (E.globalRamifiedStrictMacro_from_presented RR D hclock)

    · rcases hrankTwo with ⟨R2⟩
      exact .ramifiedStrictMacro
        (R2.globalRamifiedStrictMacro_from_presented RR D hsrepair)

end

end HC4.Valuation
