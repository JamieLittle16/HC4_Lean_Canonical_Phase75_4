import HC4.Valuation.AdaptiveAlignedSmithBoundaryReentry
import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalFirstWall
import HC4.Valuation.AdaptiveAlignedSmithSurvivingPacket
import Mathlib.Tactic

/-!
# First assembled aligned-Smith local dispatcher

This file is the first dispatcher-facing assembly of the new aligned-Smith
engine.

Starting from one scale-aware adaptive geometric state, the already-green
machinery is composed without inventing any progress relation.

The old three-way top-level classifier

    blocker | surviving wall | section boundary

is refined as follows.

* A blocker is reduced to either a general surviving Smith-grade shape or an
  actual recentered scalar first-wall competition.
* A surviving wall is reduced to either the existing refined blocker or a
  persistent homogeneous packet.
* A top-level section boundary is no longer retained as a terminal output:
  it already has a canonical determinant-one source-shear re-entry into an
  ordinary `AdaptiveGeometricRestartState`.

Thus the local aligned-Smith engine is exposed through five honest outcomes.
The next assembly layer will consume the persistent packet by the `D = 2`
saturated route or the `D >= 3` rigid/rank-two route.

No claim of strict global decrease is made in this file.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Exhaustive local output of the assembled aligned-Smith engine before
packet degree splitting and before any global well-foundedness claim.

The scalar functional `base` occurs only in the blocker first-wall branch.
It is intentionally explicit: at this stage we have a correct finite
first-wall competition for any scalar functional, but we have not yet
identified an arbitrary scalar functional with a realizable geometric wall.
-/
inductive AdaptiveAlignedSmithLocalOutcome
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (base : SmithSupportExponent → ℤ) : Prop

  /-- The blocker outcome itself already has the general surviving Smith
  grade shape. -/
  | blockerSurvivingShape
      (B : AdaptiveAlignedSmithBlockerEndpoint
        (K := K) s.degreeCap)
      (shape : HasGeneralSurvivingSmithGradeShape B.exponent)

  /-- A blocker has entered the genuine finite recentered scalar first-wall
  competition.  This is not yet called geometric progress because `base`
  still needs the realizability adapter. -/
  | blockerFirstWall
      (B : AdaptiveAlignedSmithBlockerEndpoint
        (K := K) s.degreeCap)
      (wall :
        HasAlignedRecenteredFirstWallCompetition
          B.aligned.endpoint.rawSpecialFiber B.exponent base)

  /-- The surviving Smith wall has refined back to one of the explicit
  blocker patterns of the legacy mixed-degree classifier. -/
  | refinedBlocker
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint
        (K := K) s)
      (B : AdaptiveAlignedSmithRefinedBlockerEndpoint
        (K := K) s W)

  /-- The surviving wall has produced a nonempty minimal homogeneous packet
  with persistent rank-one support. -/
  | persistentPacket
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint
        (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint
        (K := K) s W)

  /-- The top-level aligned section boundary is coordinate-removable.
  The actual re-entry state is `s.alignedBoundaryReentry B`. -/
  | canonicalReentry
      (B :
        AdaptiveAlignedSmithSectionBoundaryEndpoint
          (K := K)
          s.degreeCap
          s.rawDefect
          (zeroJetNormalizedFamily s.family)
          s.movingSection)

/-- **First master local dispatcher.**

Every scale-aware adaptive state has one of the five assembled local outcomes
above.

This theorem already removes the top-level section-boundary case as a
terminal: its constructor records a boundary certificate only so that the
actual state `s.alignedBoundaryReentry B` can be recovered definitionally.
-/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithLocalDispatcher
    [CharZero K]
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (base : SmithSupportExponent → ℤ) :
    AdaptiveAlignedSmithLocalOutcome s base := by
  rcases s.alignedSmithLegacyClassifierDispatcher with
    hblock | hsurvive | hboundary

  · rcases hblock with ⟨B⟩
    rcases B.survivingShape_or_firstWallCompetition base with
      hshape | hwall
    · exact
        AdaptiveAlignedSmithLocalOutcome.blockerSurvivingShape
          B hshape
    · exact
        AdaptiveAlignedSmithLocalOutcome.blockerFirstWall
          B hwall

  · rcases hsurvive with ⟨W⟩
    rcases W.refinedBlocker_or_packet s with
      hblock | hpacket
    · rcases hblock with ⟨B⟩
      exact
        AdaptiveAlignedSmithLocalOutcome.refinedBlocker
          W B
    · rcases hpacket with ⟨P⟩
      exact
        AdaptiveAlignedSmithLocalOutcome.persistentPacket
          W P

  · rcases hboundary with ⟨B⟩
    exact
      AdaptiveAlignedSmithLocalOutcome.canonicalReentry B

end

end HC4.Valuation
