import HC4.Valuation.AdaptiveAlignedSmithPacketProgressBridge
import HC4.Valuation.AdaptiveAlignedSmithStateBridge
import Mathlib.Tactic

/-!
# Removing the artificial rank-one analysis-view seam

`AdaptiveAlignedSmithPacketRepair` introduced

    P.rankOneAnalysisState s W complexity

only because the fixed-degree packet classifier is phrased at the bookkeeping
state `rankOneRepairState complexity`.  That object deliberately changes no
polynomial geometry, but until now the progress bridge compared the rank-two
successor to this *analysis view* rather than to the actual aligned adaptive
state.

The aligned endpoint itself inherits the incoming repair field unchanged.
Hence, whenever the outer episode is honestly at the rank-one repair stage,

    s.repair = rankOneRepairState complexity,

the analysis view is literally equal to the actual aligned adaptive state.
This file records that equality and rewrites the already-green rank-two
progress theorem so its source is the genuine aligned state.

This is intentionally stage-sensitive.  It does NOT assert that every
adaptive state is rank-one.  The eventual master dispatcher must respect the
repair stage instead of resetting it silently.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Replacing the repair field by the value it already has changes no state.

This small extensional lemma lets later adapters remove bookkeeping-only
`withRepair` views without touching the geometric proof fields.
-/
theorem AdaptiveGeometricRestartState.withRepair_eq_self
    (a : AdaptiveGeometricRestartState (K := K))
    (r : RepairState)
    (h : a.repair = r) :
    a.withRepair r = a := by
  cases a
  cases h
  rfl

/-- At an honest rank-one episode stage, the temporary packet-analysis view
is exactly the actual aligned adaptive state.

No family, section, clock, degree bound, source complexity, or proof datum is
being transported here: the two structures are equal.
-/
theorem AdaptiveAlignedSmithPersistentPacketEndpoint.rankOneAnalysisState_eq_alignedState
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ)
    (hsrepair :
      s.repair = rankOneRepairState complexity) :
    P.rankOneAnalysisState s W complexity =
      W.original.aligned.toAdaptiveState s := by
  unfold AdaptiveAlignedSmithPersistentPacketEndpoint.rankOneAnalysisState
  apply AdaptiveGeometricRestartState.withRepair_eq_self
  exact
    (AdaptiveAlignedSmithMinimalZeroJetEndpoint.toAdaptiveState_repair
      s W.original.aligned).trans hsrepair

/-- **Rank-two promotion is strict progress from the actual aligned state.**

This closes the bookkeeping gap in the previous progress bridge.  The only
extra hypothesis is the honest outer-stage invariant saying that the incoming
scale-aware episode is currently at `rankOneRepairState complexity`.

The comparison is still made after the aligned Smith macro has produced its
ordinary adaptive state.  No claim is made here that the aligned macro itself
is a strict fixed-scale step from the pre-macro state.
-/
theorem AdaptiveAlignedSmithRankTwoPacketEndpoint.certifiedFixedScaleProgress_from_alignedState
    (R : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W}
    {complexity : ℕ}
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity)
    (hsrepair :
      s.repair = rankOneRepairState complexity) :
    CertifiedFixedScaleEpisodeProgress R
      R2.continuation.toAdaptiveRankTwoContinuation.successor.toScaleAware
      (W.original.aligned.toAdaptiveState s).toScaleAware := by
  have h :=
    R2.certifiedFixedScaleProgress R
  simpa only [
    P.rankOneAnalysisState_eq_alignedState
      s W complexity hsrepair
  ] using h

/-- Existential form for the progress-facing master dispatcher. -/
theorem AdaptiveAlignedSmithRankTwoPacketEndpoint.exists_strictSuccessor_from_alignedState
    (R : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W}
    {complexity : ℕ}
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity)
    (hsrepair :
      s.repair = rankOneRepairState complexity) :
    ∃ t : AdaptiveGeometricRestartState (K := K),
      CertifiedFixedScaleEpisodeProgress R
        t.toScaleAware
        (W.original.aligned.toAdaptiveState s).toScaleAware := by
  refine
    ⟨R2.continuation.toAdaptiveRankTwoContinuation.successor, ?_⟩
  exact
    R2.certifiedFixedScaleProgress_from_alignedState
      R hsrepair

end

end HC4.Valuation
