import HC4.Valuation.AdaptiveAlignedSmithCanonicalJC2FreeDispatcher
import HC4.Valuation.AdaptivePositiveKernelFixedScaleProgress
import Mathlib.Tactic

/-!
# Canonical aligned-Smith dispatcher after consuming all positive kernel slopes

The JC2-free dispatcher has removed the old rank-one terminal branch, but its
five residual blocker constructors still mix two logically different issues:

* ordinary source-level integral kernel progress, which is already completely
  understood; and
* the genuinely anisotropic geometry where no positive integral slope exists.

Before doing any branch-specific geometry we should consume the former once
and for all.  We use coordinate `3`, the common unmarked kernel coordinate
throughout the existing adaptive restart stack.  Every residual blocker source
is repackaged as its honest adaptive endpoint state.  If its maximal integral
coordinate-3 slope is positive, the generic kernel theorem gives certified
fixed-scale progress immediately.  Otherwise the branch survives only with an
explicit `AdaptiveKernelZeroSlopeObstruction`.

Thus every non-progress constructor below is genuinely zero-slope.  This is a
strictly sharper global interface for the remaining Schur-tangency,
earlier-wall, zero-Schur and rigid-packet adapters.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- Canonical unmarked coordinate used for the common source-kernel
normalisation. -/
def adaptiveCanonicalCommonKernel : Fin 4 := 3

@[simp] theorem adaptiveCanonicalCommonKernel_ne_zero :
    adaptiveCanonicalCommonKernel ≠ (0 : Fin 4) := by
  decide

/-- JC2-free canonical outcome after every available positive integral
coordinate-3 source slope has already been turned into certified progress. -/
inductive AdaptiveAlignedSmithCanonicalZeroSlopeOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | strict
      (h : ∃ source target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        CertifiedFixedScaleEpisodeProgress RR target source)

  | reentry
      (t : AdaptiveGeometricRestartState (K := K))

  | zeroDefect
      (t : AdaptiveGeometricRestartState (K := K))
      (hzero : t.defect = 0)

  | blockerSchurEarlyActualLayerZeroSlope
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
      (hlt : C.firstActualLayerOrder < B.aligned.endpoint.defect)
      (Z : AdaptiveKernelZeroSlopeObstruction
        (B.aligned.toAdaptiveState s) adaptiveCanonicalCommonKernel)

  | blockerSchurEarlierWallZeroSlope
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
      (D : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingAlignedSquareSourceData C)
      (hwall : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareEarlierWall D)
      (Z : AdaptiveKernelZeroSlopeObstruction
        (B.aligned.toAdaptiveState s) adaptiveCanonicalCommonKernel)

  | blockerZeroSchurClosingZeroSlope
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B)
      (Z : AdaptiveKernelZeroSlopeObstruction
        (B.aligned.toAdaptiveState s) adaptiveCanonicalCommonKernel)

  | blockerPlanarRigidPacketZeroSlope
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket (0 : Fin 4) 1 2 P.degree P.packet)
      (Z : AdaptiveKernelZeroSlopeObstruction
        (B.aligned.toAdaptiveState s) adaptiveCanonicalCommonKernel)

  | blockerWSquareRigidPacketZeroSlope
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket (0 : Fin 4) 3 2 P.degree P.packet)
      (Z : AdaptiveKernelZeroSlopeObstruction
        (B.aligned.toAdaptiveState s) adaptiveCanonicalCommonKernel)

/-- Normalise one blocker-originated residual through the common source
kernel.  Positive maximal slope is consumed as strict progress; zero slope is
returned to the branch-specific geometry. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalZeroSlopeDispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalZeroSlopeOutcome RR s complexity := by
  rcases s.alignedSmithCanonicalJC2FreeDispatcher RR complexity hsrepair with
    hstrict |
    ⟨t⟩ |
    ⟨t, hzero⟩ |
    ⟨B, C, hlt⟩ |
    ⟨B, C, D, hwall⟩ |
    ⟨B, C⟩ |
    ⟨B, hall, P, hrigid⟩ |
    ⟨B, hall, P, hrigid⟩

  · exact .strict hstrict
  · exact .reentry t
  · exact .zeroDefect t hzero

  · let a := B.aligned.toAdaptiveState s
    rcases a.certifiedStrict_or_zeroSlope
        RR adaptiveCanonicalCommonKernel adaptiveCanonicalCommonKernel_ne_zero with
      ⟨target, hprogress⟩ | hzeroSlope
    · exact .strict ⟨a.toScaleAware, target, hprogress⟩
    · exact .blockerSchurEarlyActualLayerZeroSlope B C hlt hzeroSlope

  · let a := B.aligned.toAdaptiveState s
    rcases a.certifiedStrict_or_zeroSlope
        RR adaptiveCanonicalCommonKernel adaptiveCanonicalCommonKernel_ne_zero with
      ⟨target, hprogress⟩ | hzeroSlope
    · exact .strict ⟨a.toScaleAware, target, hprogress⟩
    · exact .blockerSchurEarlierWallZeroSlope B C D hwall hzeroSlope

  · let a := B.aligned.toAdaptiveState s
    rcases a.certifiedStrict_or_zeroSlope
        RR adaptiveCanonicalCommonKernel adaptiveCanonicalCommonKernel_ne_zero with
      ⟨target, hprogress⟩ | hzeroSlope
    · exact .strict ⟨a.toScaleAware, target, hprogress⟩
    · exact .blockerZeroSchurClosingZeroSlope B C hzeroSlope

  · let a := B.aligned.toAdaptiveState s
    rcases a.certifiedStrict_or_zeroSlope
        RR adaptiveCanonicalCommonKernel adaptiveCanonicalCommonKernel_ne_zero with
      ⟨target, hprogress⟩ | hzeroSlope
    · exact .strict ⟨a.toScaleAware, target, hprogress⟩
    · exact .blockerPlanarRigidPacketZeroSlope B hall P hrigid hzeroSlope

  · let a := B.aligned.toAdaptiveState s
    rcases a.certifiedStrict_or_zeroSlope
        RR adaptiveCanonicalCommonKernel adaptiveCanonicalCommonKernel_ne_zero with
      ⟨target, hprogress⟩ | hzeroSlope
    · exact .strict ⟨a.toScaleAware, target, hprogress⟩
    · exact .blockerWSquareRigidPacketZeroSlope B hall P hrigid hzeroSlope

end

end HC4.Valuation
