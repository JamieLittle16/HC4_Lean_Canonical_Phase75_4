import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction

/-!
# A18.5.90: exact producer interface for the final presented terminal

A18.5.89 packages the three unconditional polynomial contradictions available
to the terminal endgame.  The remaining semantic work is therefore no longer
"prove rank three is impossible" in the abstract.  It is exactly to extract
one honest polynomial obstruction from each of the two normalized presented
endpoint families.

This file separates those two extraction obligations and proves that any
completed pair closes every presented terminal.  The structure is deliberately
lossless: the producer receives the actual endpoint object together with its
complete retained rank-three geometry.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The two remaining terminal extraction obligations.  A blocker and a
surviving wall may use different unconditional endpoint theorems; each only
has to return one of the verified A18.5.89 polynomial obstructions. -/
structure AdaptiveAlignedSmithCanonicalTerminalObstructionProducer
    (RR : RepairRanking) (complexity : ℕ) where
  blocker :
    ∀ {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (D : AdaptiveAlignedSmithCanonicalPresentedBlocker (K := K) source)
      (geometry : AdaptiveAlignedSmithCanonicalPresentedBlockerAllRankThreeGeometry
        RR D complexity),
      Nonempty
        (AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction (K := K))
  surviving :
    ∀ {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (D : AdaptiveAlignedSmithCanonicalPresentedSurviving (K := K) source)
      (geometry : AdaptiveAlignedSmithCanonicalPresentedSurvivingAllRankThreeGeometry
        RR D complexity),
      Nonempty
        (AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction (K := K))

/-- A completed blocker/surviving obstruction producer makes every normalized
presented rank-three terminal contradictory. -/
theorem AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.impossible_of_obstructionProducer
    [IsAlgClosed K]
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity)
    (P : AdaptiveAlignedSmithCanonicalTerminalObstructionProducer
      (K := K) RR complexity) : False := by
  cases T with
  | blocker D geometry =>
      exact (Classical.choice (P.blocker D geometry)).impossible
  | surviving D geometry =>
      exact (Classical.choice (P.surviving D geometry)).impossible

/-- Producer-facing form of A18.5.75: once the two normalized terminal endpoint
families expose honest polynomial obstructions, every rank-one termination
trace is impossible. -/
theorem AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.impossible_of_obstructionProducer
    [IsAlgClosed K]
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (trace : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source)
    (P : AdaptiveAlignedSmithCanonicalTerminalObstructionProducer
      (K := K) RR complexity) : False :=
  trace.impossible_of_presentedTerminal_impossible
    (fun T => T.impossible_of_obstructionProducer P)

end

end HC4.Valuation
