import HC4.Valuation.AdaptiveAlignedSmithCanonicalChartDispatcher
import HC4.Valuation.AdaptiveAlignedSmithRankOneDirectClosingLongitudinalTerminalImpossible
import Mathlib.Tactic

/-!
# JC2-free canonical aligned-Smith dispatcher

The chart-lossless canonical dispatcher still exposes a rank-one Schur
`blockerSchurClosing` constructor.  The direct-closing analysis is now closed:
for its exact source carrier `C`, the first actual source layer is either
strictly earlier than the Hessian defect, or equality has already produced a
concrete canonical earlier coefficient/section wall.

This file consumes the old closing constructor at the global dispatcher
boundary.  In particular there is no terminal rank-one Schur constructor in
the outcome below and therefore no route from this dispatcher to the old
planar/JC2 terminal interface.

The two new Schur-frontier constructors deliberately retain the blocker and
exact source carrier.  The next restart adapter needs this provenance to turn
an actual-layer or earlier-wall witness into an ordinary adaptive successor.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- Canonical episode outcome after consuming the complete JC2-free rank-one
Schur closing theorem.

The remaining constructors are either already-certified progress/re-entry,
literal defect zero, or the three other blocker geometries which still need
their own global adapters. -/
inductive AdaptiveAlignedSmithCanonicalJC2FreeOutcome
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

  /-- The first honest source deformation already occurs strictly before the
  determinant-closing order.  This is the positive-layer restart input. -/
  | blockerSchurEarlyActualLayer
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
      (hlt : C.firstActualLayerOrder < B.aligned.endpoint.defect)

  /-- Equality `j = Delta` has been completely consumed and can only leave a
  concrete earlier coefficient/section wall on the canonical square ray. -/
  | blockerSchurEarlierWall
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
      (D : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingAlignedSquareSourceData C)
      (hwall : AdaptiveAlignedSmithRankOneClosingSourceCarrier.DirectClosingCanonicalSquareEarlierWall D)

  | blockerZeroSchurClosing
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (C : AdaptiveAlignedSmithZeroSchurClosingSourceCarrier B)

  | blockerPlanarRigidPacket
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)

  | blockerWSquareRigidPacket
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

/-- **Global canonical dispatcher with the rank-one Schur terminal branch
removed.**

This theorem is purely an assembly theorem: exact source/chart provenance is
already supplied by `alignedSmithCanonicalChartDispatcher`, and the new local
closure theorem consumes its Schur-closing constructor immediately. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalJC2FreeDispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalJC2FreeOutcome RR s complexity := by
  rcases s.alignedSmithCanonicalChartDispatcher RR complexity hsrepair with
    hstrict |
    ⟨t⟩ |
    ⟨t, hzero⟩ |
    ⟨B, C⟩ |
    ⟨B, C⟩ |
    ⟨B, hall, P, hrigid⟩ |
    ⟨B, hall, P, hrigid⟩

  · exact .strict hstrict
  · exact .reentry t
  · exact .zeroDefect t hzero

  · rcases C.firstActualLayer_strict_or_canonicalEarlierWall with
      hlt | ⟨D, hwall⟩
    · exact .blockerSchurEarlyActualLayer B C hlt
    · exact .blockerSchurEarlierWall B C D hwall

  · exact .blockerZeroSchurClosing B C
  · exact .blockerPlanarRigidPacket B hall P hrigid
  · exact .blockerWSquareRigidPacket B hall P hrigid

end

end HC4.Valuation
