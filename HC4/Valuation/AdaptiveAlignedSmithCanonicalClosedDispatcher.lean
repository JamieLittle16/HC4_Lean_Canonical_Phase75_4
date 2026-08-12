import HC4.Valuation.AdaptiveAlignedSmithCanonicalPacketDispatcher
import HC4.Valuation.AdaptiveAlignedSmithBlockerEndgame
import Mathlib.Tactic

/-!
# Canonical aligned-Smith dispatcher with the blocker branch closed

The previous packet-expanded dispatcher still exposed a `mixedDegreeBlocker`
constructor.  The local blocker geometry is now exhausted, so this file
replaces that constructor by the closed blocker endgame.

All nonblocker packet/re-entry outputs are retained unchanged.  This is an
assembly checkpoint: it proves that no opaque canonical blocker remains in
the reachable aligned-Smith dispatcher.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

inductive AdaptiveAlignedSmithCanonicalClosedOutcome
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) : Prop

  | blockerEndgame
      (B : AdaptiveAlignedSmithBlockerEndpoint (K := K) s.degreeCap)
      (h : AdaptiveAlignedSmithBlockerEndgameOutcome RR B complexity)

  | reentry
      (t : AdaptiveGeometricRestartState (K := K))

  | zeroDefect
      (t : AdaptiveGeometricRestartState (K := K))
      (hzero : t.defect = 0)

  | degreeTwoSaturated
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
      (hD : P.degree = 2)
      (S : AdaptiveAlignedSmithDegreeTwoSaturatedEndpoint (K := K) s W)

  | rigidPacket
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
      (hD : 3 ≤ P.degree)
      (R : AdaptiveAlignedSmithRigidPacketEndpoint (K := K) s W P)

  | rankTwoZeroSchur
      (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
      (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
      (hD : 3 ≤ P.degree)
      (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
        (K := K) s W P complexity)
      (M : AdaptiveAlignedSmithRankTwoMatrixEndpoint
        (K := K) s W P complexity R2)

/-- **Canonical dispatcher with no unresolved blocker constructor.**

A defect-zero blocker is exposed immediately as an ordinary defect-zero
adaptive state.  A positive-defect blocker is sent through the completely
closed local endgame theorem. -/
theorem ScaleAwareAdaptiveGeometricRestartState.alignedSmithCanonicalClosedDispatcher
    (RR : RepairRanking)
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (complexity : ℕ) :
    AdaptiveAlignedSmithCanonicalClosedOutcome RR s complexity := by
  rcases s.alignedSmithCanonicalPacketDispatcher complexity with
    ⟨B, _M, _hsame⟩ |
    ⟨t⟩ |
    ⟨t, htzero⟩ |
    ⟨W, P, hD, S⟩ |
    ⟨W, P, hD, R⟩ |
    ⟨W, P, hD, R2, M⟩

  · by_cases hz : B.aligned.endpoint.defect = 0
    · exact .zeroDefect
        (B.aligned.toAdaptiveState s)
        (by simpa using hz)
    · have hpos : 0 < B.aligned.endpoint.defect := Nat.pos_of_ne_zero hz
      exact .blockerEndgame B (B.endgame RR complexity hpos)

  · exact .reentry t

  · exact .zeroDefect t htzero

  · exact .degreeTwoSaturated W P hD S

  · exact .rigidPacket W P hD R

  · exact .rankTwoZeroSchur W P hD R2 M

end

end HC4.Valuation
