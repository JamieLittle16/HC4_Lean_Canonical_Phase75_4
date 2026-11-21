import HC4.Valuation.AdaptiveAlignedSmithCanonicalScalarZeroSchurProjectiveRankThree
import Mathlib.Tactic

/-!
# A18.4.81: packet-family rank two closes by zero or rank-three geometry

A18.4.78 transports the actual degree-at-least-three packet continuation through
its retained matrix exposure to an exact scalar zero-Schur four-block.
A18.4.80 proves that every such scalar zero-Schur block carries genuine
rank-three geometry: either a concrete nondegenerate binary block or a later
projective coefficient which leaves the kernel line of the first Schur block.

This file is the lossless composition of those two facts.  The rank-three
certificate stores the exact matrix exposure and exact zero-Schur object beside
the geometry, so no repair tag can be detached from the family on which the
rank jump was proved.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Complete rank-three continuation of one actual packet-family rank-two
endpoint. -/
structure AdaptiveAlignedSmithCanonicalPacketRankThreeProgress
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ)
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity)
    (hD : 3 ≤ P.degree) : Type (u + 1) where
  matrix : AdaptiveAlignedSmithRankTwoMatrixEndpoint
    (K := K) s W P complexity R2
  zeroSchur : ExactZeroSchurFourBlockData K
  zeroSchur_eq :
    zeroSchur = matrix.toExactZeroSchurAutomatic s W P complexity R2 hD
  geometry :
    AdaptiveAlignedSmithCanonicalCompleteScalarRankThreeGeometry
      zeroSchur complexity

/-- Lossless packet-family rank-three outcome. -/
inductive AdaptiveAlignedSmithCanonicalPacketRankThreeOutcome
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ)
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity)
    (hD : 3 ≤ P.degree) : Type (u + 1)
  | zeroDefect
      (hzero : (P.rankOneAnalysisState s W complexity).defect = 0)
  | rankThree
      (D : AdaptiveAlignedSmithCanonicalPacketRankThreeProgress
        s W P complexity R2 hD)

/-- **Degree-at-least-three packet rank two -> zero defect or complete
rank-three geometry.** -/
noncomputable def
    AdaptiveAlignedSmithRankTwoPacketEndpoint.rankThreeClosure
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ)
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity)
    (hD : 3 ≤ P.degree) :
    AdaptiveAlignedSmithCanonicalPacketRankThreeOutcome
      s W P complexity R2 hD := by
  cases R2.toExactZeroSchurOutcome s W P complexity hD with
  | zeroDefect hzero =>
      exact .zeroDefect hzero
  | exactZeroSchur hD' M Z hZ =>
      let G := exactScalarZeroSchur_completeRankThreeGeometry Z complexity
      exact .rankThree {
        matrix := M
        zeroSchur := Z
        zeroSchur_eq := by simpa using hZ
        geometry := G
      }

end

end HC4.Valuation
