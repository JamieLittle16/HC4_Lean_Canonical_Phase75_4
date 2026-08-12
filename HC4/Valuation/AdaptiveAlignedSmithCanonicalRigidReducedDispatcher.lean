import HC4.Valuation.AdaptiveAlignedSmithCanonicalEpisodeReduction
import HC4.Valuation.AdaptiveAlignedSmithRigidPacketExposureClosing
import Mathlib.Tactic

/-!
# Canonical aligned-Smith dispatcher after consuming surviving rigid packets

`AdaptiveAlignedSmithCanonicalEpisodeReduction` already consumes every
certified `D = 2` and rank-two repair exit into the well-founded episode
order.  Its only surviving-state local geometry is the `rigidPacket`
constructor.

The adaptive exposure theorem now closes that constructor honestly on the
actual exposed family:

* literal zero Hessian defect;
* same-family rank-one -> rank-two repair progress;
* a source-honest exact zero-Schur closing endpoint.

This file consumes the first two alternatives.  In particular, after this
layer there is no raw surviving rigid packet in the global dispatcher.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- Canonical episode outcome after the surviving rigid-packet geometry has
also been consumed.

The only new residual object is the source-honest zero-Schur closing endpoint
built on the actual adaptive Smith exposure. -/
inductive AdaptiveAlignedSmithCanonicalRigidReducedOutcome
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

  | rigidZeroSchurClosing
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
      (hD : 3 ≤ P.degree)
      (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)
      (h : Nonempty
        (AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint
          (K := K) s W P R))

/-- **The surviving rigid-packet constructor is eliminated.**

At the honest outer rank-one repair stage, every output of the episode-reduced
canonical dispatcher is either already one of its residual closing/re-entry
objects, or a certified fixed-scale episode descent.  In the surviving rigid
case, the adaptive exposure theorem gives zero defect, rank-two repair, or a
source-honest zero-Schur closing endpoint; the first two are consumed here. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalRigidReducedDispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalRigidReducedOutcome RR s complexity := by
  rcases s.alignedSmithCanonicalEpisodeDispatcher RR complexity hsrepair with
    hstrict |
    ⟨t⟩ |
    ⟨t, hzero⟩ |
    ⟨B, hclose⟩ |
    ⟨B, Z, hzeroClose⟩ |
    ⟨B, P, hrigid⟩ |
    ⟨B, P, hrigid⟩ |
    ⟨W, P, hD, R⟩

  · exact .strict hstrict

  · exact .reentry t

  · exact .zeroDefect t hzero

  · exact .blockerSchurClosing B hclose

  · exact .blockerZeroSchurClosing B Z hzeroClose

  · exact .blockerPlanarRigidPacket B P hrigid

  · exact .blockerWSquareRigidPacket B P hrigid

  · rcases
      AdaptiveAlignedSmithRigidPacketEndpoint.zeroDefect_or_rankTwoProgress_or_closing
        (K := K) s W P R hD complexity with
      hzero | hrepair | hclosing
    · exact .zeroDefect (W.original.aligned.toAdaptiveState s) hzero
    · let a := W.original.aligned.toAdaptiveState s
      have hastage : a.repair = rankOneRepairState complexity := by
        simpa [a] using hsrepair
      rcases
          a.exists_certifiedRankTwoRepairSuccessor
            RR complexity hastage hrepair with
        ⟨target, hprogress⟩
      exact .strict
        ⟨a.toScaleAware, target.toScaleAware, hprogress⟩
    · exact .rigidZeroSchurClosing W P hD R hclosing

end

end HC4.Valuation
