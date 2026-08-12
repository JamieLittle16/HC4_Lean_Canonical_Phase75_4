import HC4.Valuation.CertifiedFixedScaleRestartEpisodeProgress
import HC4.Valuation.AdaptiveAlignedSmithPacketRepair
import Mathlib.Tactic

/-!
# Aligned rank-two packet -> certified fixed-scale progress

The aligned Smith packet machinery already produces

`AdaptiveAlignedSmithRankTwoPacketEndpoint`

whose `continuation` field is an `AdaptiveRankTwoFamilyContinuation`.
That structure extends the geometry-carrying `AdaptiveRankTwoContinuation`,
and the latter now has a compiled theorem saying that its repair successor is
strict progress in every certified fixed-scale episode order.

This file is therefore only an adapter.  It makes the strict recursive exit
visible directly at the aligned packet layer.

Importantly, the progress comparison starts from the packet's
`rankOneAnalysisState`.  We do **not** claim that the preceding aligned-Smith
normalisations are themselves strict progress; they remain internal moves of
the eventual macro episode.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- A provenance-strengthened rank-two family continuation has the same
strict repair successor as its underlying `AdaptiveRankTwoContinuation`. -/
theorem AdaptiveRankTwoFamilyContinuation.certifiedFixedScaleProgress
    (R : RepairRanking)
    {s : AdaptiveGeometricRestartState (K := K)}
    {D complexity : ℕ}
    {Q : MvPolynomial (Fin 4) K}
    (c : AdaptiveRankTwoFamilyContinuation s D complexity Q) :
    CertifiedFixedScaleEpisodeProgress R
      c.toAdaptiveRankTwoContinuation.successor.toScaleAware
      s.toScaleAware := by
  exact
    AdaptiveRankTwoContinuation.certifiedFixedScaleProgress
      (K := K) R c.toAdaptiveRankTwoContinuation

/-- **Aligned packet rank-two promotion is genuine well-founded progress.**

The source is the actual same-family rank-one analysis state retained by the
packet endpoint.  The target changes only its repair coordinate to the
rank-two repair state.  The strictness certificate is the intrinsic
`RepairProgress` already stored in the continuation.
-/
theorem AdaptiveAlignedSmithRankTwoPacketEndpoint.certifiedFixedScaleProgress
    (R : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W}
    {complexity : ℕ}
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity) :
    CertifiedFixedScaleEpisodeProgress R
      R2.continuation.toAdaptiveRankTwoContinuation.successor.toScaleAware
      (P.rankOneAnalysisState s W complexity).toScaleAware := by
  exact
    AdaptiveRankTwoFamilyContinuation.certifiedFixedScaleProgress
      (K := K) R R2.continuation

/-- Existential form convenient for a progress-facing dispatcher: every
aligned rank-two packet endpoint contains an ordinary adaptive successor
strictly below its rank-one analysis state. -/
theorem AdaptiveAlignedSmithRankTwoPacketEndpoint.exists_strictSuccessor
    (R : RepairRanking)
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s}
    {P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W}
    {complexity : ℕ}
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity) :
    ∃ t : AdaptiveGeometricRestartState (K := K),
      CertifiedFixedScaleEpisodeProgress R
        t.toScaleAware
        (P.rankOneAnalysisState s W complexity).toScaleAware := by
  refine
    ⟨R2.continuation.toAdaptiveRankTwoContinuation.successor, ?_⟩
  exact R2.certifiedFixedScaleProgress R

end

end HC4.Valuation
