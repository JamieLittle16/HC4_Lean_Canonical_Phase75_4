import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalBoundaryEndpointProvenance
import Mathlib.Tactic

/-!
# A18.4.29: one source-honest presented canonical endpoint

A18.4.28 restores the exact clock/family/section equations erased by the old
coupled-wall outcome.  The primitive and coupled boundary branches can now be
forgotten uniformly: both produce an actual scale-aware state which is a pure
ramified presentation of the incoming source and whose family is literally the
canonical endpoint family already classified as blocker or surviving.

This file packages that common interface.  It does not continue the endpoint
and it does not call a presentation progress.  Its only purpose is to make the
next local-continuation theorem independent of whether the endpoint arose by
primitive scale-one entry or by the 20-fold coupled pointed presentation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- A canonical blocker represented as an actual scale-aware state, together
with a certified pure presentation from the original source.  The three exact
endpoint equations prevent the state and blocker geometry from drifting
apart. -/
structure AdaptiveAlignedSmithCanonicalPresentedBlocker
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  presented : ScaleAwareAdaptiveGeometricRestartState (K := K)
  sourcePresentation :
    HasCertifiedRamifiedEpisodeInternalMove presented source
  blocker : AdaptiveAlignedSmithBlockerEndpoint (K := K) presented.degreeCap
  defect_eq : blocker.aligned.endpoint.defect = presented.rawDefect
  family_eq : blocker.aligned.endpoint.family = presented.family
  movingSection_eq :
    blocker.aligned.endpoint.movingSection = presented.movingSection

/-- Surviving-wall analogue of `AdaptiveAlignedSmithCanonicalPresentedBlocker`. -/
structure AdaptiveAlignedSmithCanonicalPresentedSurviving
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  presented : ScaleAwareAdaptiveGeometricRestartState (K := K)
  sourcePresentation :
    HasCertifiedRamifiedEpisodeInternalMove presented source
  wall : AdaptiveAlignedSmithSurvivingWallEndpoint
    (K := K) presented.degreeCap
  defect_eq : wall.aligned.endpoint.defect = presented.rawDefect
  family_eq : wall.aligned.endpoint.family = presented.family
  movingSection_eq :
    wall.aligned.endpoint.movingSection = presented.movingSection

namespace AdaptiveAlignedSmithCanonicalPresentedSurviving

/-- Reattach the already-proved legacy-compatible surviving-wall certificate
on the represented state itself. -/
noncomputable def toStateEndpoint
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving source) :
    AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) D.presented where
  original := D.wall
  wall := D.wall.toAdaptiveWall D.presented
  wall_eq := rfl

@[simp]
theorem toStateEndpoint_original
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving source) :
    D.toStateEndpoint.original = D.wall := rfl

end AdaptiveAlignedSmithCanonicalPresentedSurviving

/-- Uniform output of one aligned-boundary head.  There is no boundary
constructor: the boundary has either spent strictly or has already been
absorbed into one represented canonical endpoint. -/
inductive AdaptiveAlignedSmithCanonicalPresentedBoundaryOutcome
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Prop

  | strictMacro
      (D : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source)

  | blocker
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)

  | surviving
      (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)

/-- **A18.4.29 boundary-to-presented-endpoint compression.**

Primitive endpoints are represented at the unchanged source scale.  Coupled
pointed endpoints are represented at the literal aligned absolute scale.  In
both cases the endpoint's family, clock and moving section are definitionally
or propositionally tied to the represented state before the origin tag is
forgotten. -/
theorem AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace.toPresentedEndpointOutcome
    {RR : RepairRanking}
    {source target : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalAlignedBoundaryHeadTrace
      RR source target) :
    AdaptiveAlignedSmithCanonicalPresentedBoundaryOutcome RR source := by
  cases trace.exactClosedReduction with
  | strictMacro D =>
      exact .strictMacro D

  | primitiveBlocker B₀ htail P B hEq =>
      let presented := P.toScaleOneState
      have hmove : HasCertifiedRamifiedEpisodeInternalMove presented source := by
        simpa [presented] using P.certifiedInternalMove
      exact .blocker {
        presented := presented
        sourcePresentation := hmove
        blocker := B
        defect_eq := by
          rw [hEq]
          simpa [presented] using P.defect_eq
        family_eq := by
          rw [hEq]
          simpa [presented] using P.family_eq
        movingSection_eq := by
          rw [hEq]
          simpa [presented] using P.movingSection_eq
      }

  | primitiveSurviving B₀ htail P W hEq =>
      let presented := P.toScaleOneState
      have hmove : HasCertifiedRamifiedEpisodeInternalMove presented source := by
        simpa [presented] using P.certifiedInternalMove
      exact .surviving {
        presented := presented
        sourcePresentation := hmove
        wall := W.original
        defect_eq := by
          rw [hEq]
          simpa [presented] using P.defect_eq
        family_eq := by
          rw [hEq]
          simpa [presented] using P.family_eq
        movingSection_eq := by
          rw [hEq]
          simpa [presented] using P.movingSection_eq
      }

  | coupledBlocker B₀ htail P E hdef hfam hsec B hEq =>
      let presented := E.toOuterScaleAwareState source
      have hmove : HasCertifiedRamifiedEpisodeInternalMove presented source := by
        simpa [presented] using
          E.hasCertifiedOuterInternal_of_exactClock hdef
      exact .blocker {
        presented := presented
        sourcePresentation := hmove
        blocker := B
        defect_eq := by
          rw [hEq]
          rfl
        family_eq := by
          rw [hEq]
          rfl
        movingSection_eq := by
          rw [hEq]
          rfl
      }

  | coupledSurviving B₀ htail P E hdef hfam hsec W hEq =>
      let presented := E.toOuterScaleAwareState source
      have hmove : HasCertifiedRamifiedEpisodeInternalMove presented source := by
        simpa [presented] using
          E.hasCertifiedOuterInternal_of_exactClock hdef
      exact .surviving {
        presented := presented
        sourcePresentation := hmove
        wall := W
        defect_eq := by
          rw [hEq]
          rfl
        family_eq := by
          rw [hEq]
          rfl
        movingSection_eq := by
          rw [hEq]
          rfl
      }

end

end HC4.Valuation
