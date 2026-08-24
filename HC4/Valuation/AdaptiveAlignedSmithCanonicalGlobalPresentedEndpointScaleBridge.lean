import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalPresentedBoundaryEndpoint
import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalSurvivingRankTwoAbsoluteScale
import Mathlib.Tactic

/-!
# A18.4.30: keep presented canonical endpoints at their current absolute scale

A18.4.29 packages a boundary-produced canonical blocker/surviving endpoint as
an actual scale-aware state.  The next local continuation must not run the
aligned Smith transformation again merely to recover the endpoint state: that
would introduce an artificial extra factor `20`.

This file proves the exact state identity needed to reuse the already-green
fixed-scale local geometry at the endpoint's *current* absolute scale.  It
then applies that identity to the direct surviving rank-two packet branch.
The target is the actual geometry-carrying rank-two continuation family,
recorded at the same absolute scale as the presented endpoint; the stored
source presentation is prefixed afterwards.

No new ramification, homogeneity assumption, or repair-only relabel is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## The represented endpoint really is the current state -/

/-- Re-recording a presented blocker endpoint's ordinary adaptive state at the
stored absolute scale gives literally the stored presented state.  In
particular the polynomial family is not silently changed by a bookkeeping
certificate. -/
theorem AdaptiveAlignedSmithCanonicalPresentedBlocker.endpointScaleAware_eq_presented
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source) :
    (D.blocker.aligned.toAdaptiveState D.presented).toScaleAwareAt
        D.presented.scale D.presented.scale_pos =
      D.presented := by
  apply ScaleAwareAdaptiveGeometricRestartState.ext <;>
    simp [AdaptiveGeometricRestartState.toScaleAwareAt,
      AdaptiveAlignedSmithMinimalZeroJetEndpoint.toAdaptiveState,
      D.defect_eq, D.family_eq, D.movingSection_eq]

/-- Surviving-wall analogue of
`AdaptiveAlignedSmithCanonicalPresentedBlocker.endpointScaleAware_eq_presented`.
The exact canonical endpoint family, section and determinant clock are already
the current represented state. -/
theorem AdaptiveAlignedSmithCanonicalPresentedSurviving.endpointScaleAware_eq_presented
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source) :
    (D.wall.aligned.toAdaptiveState D.presented).toScaleAwareAt
        D.presented.scale D.presented.scale_pos =
      D.presented := by
  apply ScaleAwareAdaptiveGeometricRestartState.ext <;>
    simp [AdaptiveGeometricRestartState.toScaleAwareAt,
      AdaptiveAlignedSmithMinimalZeroJetEndpoint.toAdaptiveState,
      D.defect_eq, D.family_eq, D.movingSection_eq]

/-! ## Direct surviving rank-two continuation at the represented scale -/

/-- A geometry-carrying rank-two packet on a presented surviving endpoint is
strict progress at the endpoint's *existing* absolute scale.

The legacy packet theorem is fixed-scale on ordinary adaptive states.  We lift
it to `D.presented.scale`, rewrite its source by the exact state identity
above, and only then prefix the pure presentation from the original source.
Thus the recursive target contains the actual rank-two continuation family and
there is no second aligned-Smith ramification. -/
theorem AdaptiveAlignedSmithRankTwoPacketEndpoint.globalRamifiedStrictMacro_from_presented
    (RR : RepairRanking)
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint
      (K := K) D.presented D.toStateEndpoint}
    {complexity : ℕ}
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) D.presented D.toStateEndpoint P complexity)
    (hsrepair : source.repair = rankOneRepairState complexity) :
    AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro RR source := by
  let W := D.toStateEndpoint
  let a := W.original.aligned.toAdaptiveState D.presented

  have hpresentedRepair :
      D.presented.repair = rankOneRepairState complexity := by
    change D.presented.repair = rankOneRepairState complexity
    rcases D.sourcePresentation with ⟨hmove⟩
    rw [hmove.repair_eq]
    exact hsrepair

  have hfixed :
      CertifiedFixedScaleEpisodeProgress RR
        R2.continuation.toAdaptiveRankTwoContinuation.successor.toScaleAware
        a.toScaleAware := by
    simpa [W, a] using
      R2.certifiedFixedScaleProgress_from_alignedState RR hpresentedRepair

  have hlift :=
    CertifiedFixedScaleEpisodeProgress.toSameScaleAt
      (K := K) RR hfixed D.presented.scale D.presented.scale_pos

  have hsourceEq :
      a.toScaleAwareAt D.presented.scale D.presented.scale_pos =
        D.presented := by
    simpa [W, a] using D.endpointScaleAware_eq_presented
  rw [hsourceEq] at hlift

  let target :=
    R2.continuation.toAdaptiveRankTwoContinuation.successor.toScaleAwareAt
      D.presented.scale D.presented.scale_pos

  have hprogress :
      CertifiedSameScaleEpisodeProgress RR target D.presented := by
    simpa [target] using hlift

  let local : AdaptiveAlignedSmithCanonicalGlobalRamifiedStrictMacro
      RR D.presented :=
    .mk D.presented target
      (HasCertifiedRamifiedEpisodeInternalMove.identity D.presented)
      hprogress

  exact local.prepend_internal RR D.sourcePresentation

/-- Regression check: the direct presented rank-two target is still the
literal family built by the local rank-two continuation, not a repair-only
copy of the presented source. -/
@[simp]
theorem AdaptiveAlignedSmithRankTwoPacketEndpoint.presentedTarget_family
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint
      (K := K) D.presented D.toStateEndpoint}
    {complexity : ℕ}
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) D.presented D.toStateEndpoint P complexity) :
    (R2.continuation.toAdaptiveRankTwoContinuation.successor.toScaleAwareAt
      D.presented.scale D.presented.scale_pos).family =
      R2.continuation.toAdaptiveRankTwoContinuation.successor.family := by
  rfl

end

end HC4.Valuation
