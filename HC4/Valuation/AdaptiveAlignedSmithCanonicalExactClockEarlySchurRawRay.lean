import HC4.Valuation.AdaptiveAlignedSmithCanonicalExactClockFinalLocalCore
import HC4.Valuation.AdaptiveAlignedSmithRankOneSchurTangentialRawRay
import Mathlib.Tactic

/-!
# Raw Schur-ray prefix on the exact-clock final local problem

The final local core retains an `earlySchurTangential` constructor only when
an honest rank-one closing carrier has a genuine source layer strictly below
the determinant-closing defect. The aligned clock already proves every order
below that defect is Schur-tangential.

This file attaches the whole denominator-free raw-ray prefix to the final
local problem without changing its five-way geometry type.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- Source-safe raw-ray data required from an early Schur constructor of a
final local problem.  The statement is written out explicitly here rather
than through the carrier-local prefix abbreviation, so this final-local
wrapper is insensitive to namespace/field-notation elaboration. -/
def AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem.HasEarlySchurRawRayPrefix
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s) : Prop :=
  ∀ (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier P.stationary.blocker)
      (hlt : C.firstActualLayerOrder < P.stationary.blocker.aligned.endpoint.defect)
      (htangential :
        C.IsClosingClockSchurTangentialOrder C.firstActualLayerOrder),
    P.geometry =
        AdaptiveAlignedSmithCanonicalExactClockFinalLocalGeometry.earlySchurTangential
          C hlt htangential →
      ∀ n : ℕ,
        n < P.stationary.blocker.aligned.endpoint.defect →
          HasAdaptiveAlignedRawSchurRayAtOrder C.chartData n

namespace AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem

/-- Every exact-clock final local problem already satisfies the raw-ray
prefix requirement on its early Schur branch. -/
theorem hasEarlySchurRawRayPrefix
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem s) :
    P.HasEarlySchurRawRayPrefix := by
  intro C hlt htangential hgeometry n hn
  exact
    AdaptiveAlignedSmithRankOneClosingSourceCarrier.rawSchurRayAtOrder_of_lt_defect
      C hn

end AdaptiveAlignedSmithCanonicalExactClockFinalLocalProblem

end

end HC4.Valuation
