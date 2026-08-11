import HC4.Valuation.AdaptiveAlignedSmithPacketRepair
import HC4.Valuation.AdaptiveRankTwoMatrixExposure
import Mathlib.Tactic

/-!
# Aligned rank-two packet to the existing matrix-exposure interface

The aligned surviving-wall programme now reaches an
`AdaptiveRankTwoFamilyContinuation` carrying the exact integral Smith wall
and the exact balanced-subface provenance.

The existing `AdaptiveRankTwoFamilyContinuation.toMatrixExposure` constructor
therefore applies directly.  Its only additional input is the natural
nonnegative integral wall level and one adaptive exposure ramification
certificate.

As elsewhere, the adaptive state type itself does not assert positivity of
the determinant clock.  The honest result is consequently:

* zero retained defect; or
* an actual `AdaptiveRankTwoMatrixExposure`.

No packet-isolation or Schur conclusion is assumed in this file.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- Actual matrix-level exposure attached to an aligned rank-two packet
endpoint. -/
structure AdaptiveAlignedSmithRankTwoMatrixEndpoint
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ)
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity) where
  commonLevel : ℕ
  commonLevel_eq :
    (commonLevel : ℤ) =
      R2.continuation.integralWall.realization.combinedSourceLevel
        R2.continuation.integralWall.level
  ramification :
    AdaptiveSmithExposureRamificationData
      R2.continuation.integralWall.realization.combinedSourceWeight
      commonLevel
      (P.rankOneAnalysisState s W complexity).defect
  exposure :
    AdaptiveRankTwoMatrixExposure
      (P.rankOneAnalysisState s W complexity)
      P.degree complexity P.packet R2.continuation

/-- Construct the existing rank-two matrix exposure whenever the retained
determinant clock is positive. -/
noncomputable def
    AdaptiveAlignedSmithRankTwoPacketEndpoint.toMatrixEndpoint
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ)
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity)
    (hdefect :
      0 < (P.rankOneAnalysisState s W complexity).defect) :
    AdaptiveAlignedSmithRankTwoMatrixEndpoint
      (K := K) s W P complexity R2 := by
  let wall := R2.continuation.integralWall
  let z : ℤ :=
    wall.realization.combinedSourceLevel wall.level
  have hz : 0 ≤ z := by
    dsimp [z, wall]
    exact
      HC4.Valuation.IntegralAdaptiveSurvivingSmithWall.combinedSourceLevel_nonnegative
        R2.continuation.integralWall
  let m : ℕ := z.toNat
  have hm : (m : ℤ) = z := by
    dsimp [m]
    exact Int.toNat_of_nonneg hz
  let ram :
      AdaptiveSmithExposureRamificationData
        wall.realization.combinedSourceWeight
        m
        (P.rankOneAnalysisState s W complexity).defect :=
    adaptiveSmithExposureRamificationData
      wall.realization.combinedSourceWeight
      m
      (P.rankOneAnalysisState s W complexity).defect
      hdefect
  have hexposure :
      AdaptiveRankTwoMatrixExposure
        (P.rankOneAnalysisState s W complexity)
        P.degree complexity P.packet R2.continuation := by
    dsimp [wall] at ram
    exact
      R2.continuation.toMatrixExposure
        m
        (by simpa [wall, z] using hm)
        ram
  exact
    {
      commonLevel := m
      commonLevel_eq := by simpa [wall, z] using hm
      ramification := by simpa [wall] using ram
      exposure := hexposure
    }

/-- **Rank-two family -> zero defect or actual matrix exposure.**

This is the direct bridge from the newly assembled aligned packet dispatcher
to the already-existing matrix/zero-Schur infrastructure. -/
theorem
    AdaptiveAlignedSmithRankTwoPacketEndpoint.zeroDefect_or_matrixExposure
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s)
    (P : AdaptiveAlignedSmithPersistentPacketEndpoint (K := K) s W)
    (complexity : ℕ)
    (R2 : AdaptiveAlignedSmithRankTwoPacketEndpoint
      (K := K) s W P complexity) :
    (P.rankOneAnalysisState s W complexity).defect = 0 ∨
      Nonempty
        (AdaptiveAlignedSmithRankTwoMatrixEndpoint
          (K := K) s W P complexity R2) := by
  by_cases hzero :
      (P.rankOneAnalysisState s W complexity).defect = 0
  · exact Or.inl hzero
  · right
    have hpos :
        0 < (P.rankOneAnalysisState s W complexity).defect :=
      Nat.pos_of_ne_zero hzero
    exact
      ⟨R2.toMatrixEndpoint s W P complexity hpos⟩

end

end HC4.Valuation
