import HC4.Valuation.AdaptiveAlignedSmithCanonicalSurvivingRigidElimination
import HC4.Valuation.AdaptiveAlignedSmithBlockerEndgameProvenance
import Mathlib.Tactic

/-!
# Lossless canonical episode dispatcher

The surviving-wall side is already completely consumed by strict episode
progress, determinant-zero, or section-boundary re-entry.  The only remaining
reason to keep a richer dispatcher is the blocker side: the compact endgame
forgets the honest right-recentered source on Schur closing branches and the
full-fibre all-`2 x 2`-minors certificate on rigid packet branches.

This file reruns only that already-green blocker endgame through its lossless
interface while consuming every already-established progress branch exactly as
before.  No new local geometry is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- Final lossless local/global frontier after all surviving-wall geometry and
all already-certified repair/defect progress have been consumed. -/
inductive AdaptiveAlignedSmithCanonicalProvenanceOutcome
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
      (source : AdaptiveAlignedSmithBlockerRecenteredSourceData B)
      (h : HasAdaptiveAlignedSmithBlockerSchurClosing B)

  | blockerZeroSchurClosing
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (source : AdaptiveAlignedSmithBlockerRecenteredSourceData B)
      (Z : ExactZeroSchurFourBlockData (MvPolynomial (Fin 4) K))
      (h : HasAdaptiveAlignedZeroSchurClosing Z)

  | blockerPlanarRigidPacket
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (hall :
        ∀ rho : Equiv.Perm (Fin 4),
          (adaptiveAlignedEndpointRightRecenteredSpecialHessianFourBlock
            rho B.aligned.endpoint).AllTwoByTwoMinorsZero)
      (P : AdaptiveAlignedSmithQuadraticCompetitorPacketEndpoint (K := K) B)
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

/-- **Lossless global canonical dispatcher.**

All surviving-wall branches are consumed into strict progress, re-entry, or
zero defect.  On the blocker side, already-certified strict and rank-two
repair exits are likewise consumed, but every genuinely closing/rigid output
retains the exact provenance needed by the final source-level restart or
terminal extraction. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalProvenanceDispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ)
    (hsrepair : s.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalProvenanceOutcome RR s complexity := by
  rcases s.alignedSmithCanonicalClosedDispatcher RR complexity with
    ⟨B, _hcompact⟩ |
    ⟨t⟩ |
    ⟨t, hzero⟩ |
    ⟨W, P, _hD, S⟩ |
    ⟨W, P, hD, R⟩ |
    ⟨W, P, _hD, R2, _M⟩

  · by_cases hz : B.aligned.endpoint.defect = 0
    · exact .zeroDefect
        (B.aligned.toAdaptiveState s)
        (by simpa using hz)
    · have hpos : 0 < B.aligned.endpoint.defect := Nat.pos_of_ne_zero hz
      rcases B.endgameWithProvenance RR complexity hpos with
        hstrict |
        hrepair |
        ⟨source, hclose⟩ |
        ⟨source, Z, hzeroClose⟩ |
        ⟨hall, P, hrigid⟩ |
        ⟨hall, P, hrigid⟩

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

      · exact .blockerSchurClosing B source hclose

      · exact .blockerZeroSchurClosing B source Z hzeroClose

      · exact .blockerPlanarRigidPacket B hall P hrigid

      · exact .blockerWSquareRigidPacket B hall P hrigid

  · exact .reentry t

  · exact .zeroDefect t hzero

  · have hstrict :=
      AdaptiveAlignedSmithDegreeTwoSaturatedEndpoint.exists_certifiedFixedScaleStrictSuccessor
        (K := K) RR P S
    dsimp only at hstrict
    rcases hstrict with ⟨target, hprogress, _hactive⟩
    exact .strict ⟨_, target, hprogress⟩

  · rcases R.zeroDefect_or_rankTwoProgress_or_closing s W P hD complexity with
      hzero | hrepair | hclosing

    · exact .zeroDefect (W.original.aligned.toAdaptiveState s) hzero

    · let a := W.original.aligned.toAdaptiveState s
      have hastage : a.repair = rankOneRepairState complexity := by
        simpa [a] using hsrepair
      rcases
          a.exists_certifiedRankTwoRepairSuccessor
            RR complexity hastage hrepair with
        ⟨target, hprogress⟩
      exact .strict ⟨a.toScaleAware, target.toScaleAware, hprogress⟩

    · let C : AdaptiveAlignedSmithRigidZeroSchurClosingEndpoint
          (K := K) s W P R := Classical.choice hclosing
      rcases C.exposure.canonicalSpecial_or_boundary with
        hspecial | hboundary

      · let a : AdaptiveGeometricRestartState (K := K) :=
          C.exposure.toAdaptiveState hspecial
        have hfree :
            ∀ d ∈ (polynomialFamilySpecialFiber a.family).support,
              d (3 : Fin 4) = 0 := by
          simpa [a] using C.specialFiber_free_three hspecial
        rcases
            a.exists_certifiedFixedScaleStrictSuccessor_of_specialFiber_free_three
              RR hfree with
          ⟨target, hprogress, _hactiveTarget⟩
        exact .strict ⟨_, target, hprogress⟩

      · let Bboundary : AdaptiveSmithExposureSectionBoundary C.exposure :=
          Classical.choice hboundary
        exact .reentry Bboundary.toAdaptiveState

  · rcases
      R2.exists_strictSuccessor_from_alignedState RR hsrepair with
      ⟨target, hprogress⟩
    exact .strict
      ⟨(W.original.aligned.toAdaptiveState s).toScaleAware,
        target.toScaleAware, hprogress⟩

end

end HC4.Valuation
