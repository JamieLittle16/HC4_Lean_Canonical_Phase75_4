import HC4.Valuation.AdaptiveAlignedSmithCanonicalClosedDispatcher
import HC4.Valuation.AdaptiveAlignedSmithDegreeTwoFixedScaleProgress
import HC4.Valuation.AdaptiveAlignedSmithRankOneStageProgress
import Mathlib.Tactic

/-!
# Canonical aligned-Smith dispatcher after consuming certified episode progress

The closed canonical dispatcher has no unresolved blocker geometry, but some
of its constructors still expose local objects which already carry genuine
well-founded progress:

* a blocker `rankTwoRepair` is same-family repair descent;
* the saturated `D = 2` branch is strict raw-defect descent after the
  canonical zero-cost ramification rebase;
* the aligned rank-two packet branch is strict repair descent from the actual
  aligned state whenever the outer episode is honestly at the rank-one repair
  stage.

This file consumes exactly those exits.  It deliberately does **not** call an
aligned/exposure coordinate change itself recursive progress: the source of a
strict exit is retained existentially.  The next global macro-step layer only
has to prove that those sources are zero-cost presentations of the incoming
state.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- Promote an abstract rank-one -> rank-two repair certificate to an actual
same-family adaptive successor.  No geometry changes. -/
theorem AdaptiveGeometricRestartState.exists_certifiedRankTwoRepairSuccessor
    (RR : RepairRanking)
    (a : AdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hstage : a.repair = rankOneRepairState complexity)
    (hrepair :
      RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity)) :
    ∃ t : AdaptiveGeometricRestartState (K := K),
      CertifiedFixedScaleEpisodeProgress RR
        t.toScaleAware a.toScaleAware := by
  let t := a.withRepair (rankTwoRepairState complexity)
  refine ⟨t, ?_⟩
  apply certifiedFixedScaleEpisodeProgress_of_repairProgress (K := K) RR
  · rfl
  · rfl
  · simpa [t, AdaptiveGeometricRestartState.toScaleAware,
      AdaptiveGeometricRestartState.withRepair, hstage] using hrepair

/-- Progress-consumed form of the local blocker endgame.

Only genuine closing/rigid alternatives remain besides an already-certified
strict successor. -/
inductive AdaptiveAlignedSmithBlockerEpisodeOutcome
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
    (complexity : ℕ) : Prop

  | strict
      (h : ∃ source target : ScaleAwareAdaptiveGeometricRestartState (K := K),
        CertifiedFixedScaleEpisodeProgress RR target source)

  | schurClosing
      (h : HasAdaptiveAlignedSmithBlockerSchurClosing B)

  | zeroSchurClosing
      (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
      (h : HasAdaptiveAlignedZeroSchurClosing Z)

  | planarRigidPacket
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)

  | wSquareRigidPacket
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

/-- Consume every already-strict local blocker alternative. -/
theorem AdaptiveAlignedSmithBlockerEndgameOutcome.toEpisodeOutcome
    (RR : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap}
    {complexity : ℕ}
    (h : AdaptiveAlignedSmithBlockerEndgameOutcome RR B complexity)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithBlockerEpisodeOutcome RR B complexity := by
  rcases h with hstrict | hrepair | hclose | ⟨Z, hzeroClose⟩ |
      ⟨P, hrigid⟩ | ⟨P, hrigid⟩

  · unfold HasAdaptiveAlignedSmithBlockerCertifiedStrictSuccessor at hstrict
    dsimp only at hstrict
    rcases hstrict with ⟨target, hprogress⟩
    exact .strict ⟨_, target, hprogress⟩

  · let a := B.aligned.toAdaptiveState s
    have hastage : a.repair = rankOneRepairState complexity := by
      simpa [a] using hsrepair
    rcases
        a.exists_certifiedRankTwoRepairSuccessor
          RR complexity hastage hrepair with
      ⟨target, hprogress⟩
    exact .strict ⟨a.toScaleAware, target.toScaleAware, hprogress⟩

  · exact .schurClosing hclose

  · exact .zeroSchurClosing Z hzeroClose

  · exact .planarRigidPacket P hrigid

  · exact .wSquareRigidPacket P hrigid

/-- Canonical dispatcher after all currently-certified episode progress has
been consumed.

The residual constructors are now semantically honest:

* `strict` really contains a well-founded fixed-scale successor;
* `reentry` is a coordinate/exposure continuation still requiring zero-cost
  macro bookkeeping;
* `zeroDefect` is the literal determinant-clock endpoint;
* the remaining blocker/packet constructors are genuine closing or rigid
  geometry, not hidden repair progress.
-/
inductive AdaptiveAlignedSmithCanonicalEpisodeOutcome
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

  | blockerSchurClosing
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (h : HasAdaptiveAlignedSmithBlockerSchurClosing B)

  | blockerZeroSchurClosing
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
      (h : HasAdaptiveAlignedZeroSchurClosing Z)

  | blockerPlanarRigidPacket
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint
        (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 1 2 P.degree P.packet)

  | blockerWSquareRigidPacket
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (P : AdaptiveAlignedSmithWSquarePacketEndpoint (K := K) B)
      (h : HasRigidRankOnePacket
        (0 : Fin 4) 3 2 P.degree P.packet)

  | rigidPacket
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
      (hD : 3 ≤ P.degree)
      (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)

/-- **Progress-facing canonical dispatcher at the honest rank-one stage.**

Both `D = 2` saturation and the rank-two packet branch have disappeared into
`strict`.  A blocker's internal rank-two-repair alternative is consumed in
the same way. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalEpisodeDispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalEpisodeOutcome RR s complexity := by
  rcases s.alignedSmithCanonicalClosedDispatcher RR complexity with
    ⟨B, hB⟩ |
    ⟨t⟩ |
    ⟨t, hzero⟩ |
    ⟨W, P, _hD, S⟩ |
    ⟨W, P, hD, R⟩ |
    ⟨W, P, _hD, R2, _M⟩

  · rcases hB.toEpisodeOutcome RR hsrepair with
      hstrict | hclose | ⟨Z, hzeroClose⟩ | ⟨P, hrigid⟩ | ⟨P, hrigid⟩
    · exact .strict hstrict
    · exact .blockerSchurClosing B hclose
    · exact .blockerZeroSchurClosing B Z hzeroClose
    · exact .blockerPlanarRigidPacket B P hrigid
    · exact .blockerWSquareRigidPacket B P hrigid

  · exact .reentry t

  · exact .zeroDefect t hzero

  · have hstrict :=
      AdaptiveAlignedSmithDegreeTwoSaturatedEndpoint.exists_certifiedFixedScaleStrictSuccessor
        (K := K) RR P S
    dsimp only at hstrict
    rcases hstrict with ⟨target, hprogress, _hactive⟩
    exact .strict ⟨_, target, hprogress⟩

  · exact .rigidPacket W P hD R

  · rcases
      R2.exists_strictSuccessor_from_alignedState RR hsrepair with
      ⟨target, hprogress⟩
    exact .strict
      ⟨(W.original.aligned.toAdaptiveState s).toScaleAware,
        target.toScaleAware, hprogress⟩

end

end HC4.Valuation
