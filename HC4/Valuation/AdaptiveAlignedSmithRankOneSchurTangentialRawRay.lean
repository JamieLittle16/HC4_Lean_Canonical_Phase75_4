import HC4.Valuation.AdaptiveAlignedSmithRankOneFirstActualLayerTangency
import HC4.Newton.SchurTangentialRawRay
import Mathlib.Tactic

/-!
# Source-safe raw Schur ray behind a tangential aligned clock

The chosen rank-one Schur clock is obtained from the raw denominator-cleared
binary Schur series by one of the two alignments in
`RankOneSchurSeriesAlignment`.  That alignment is a matrix congruence over the
source polynomial ring, not an honest source coordinate change.

For later source geometry we therefore immediately pull a tangential aligned
coefficient back to a denominator-free statement about the raw Schur block.
The output remembers only that one of the two legitimate raw pivots exists,
together with its raw-ray equations; it does not expose the proof-dependent
classical choice used to define `chosenClock`.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- Denominator-free raw-ray certificate at one parameter order of the exact
rank-one Schur chart. -/
def HasAdaptiveAlignedRawSchurRayAtOrder
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (D : AdaptiveAlignedRightRecenteredRankOneSchurChartData B)
    (n : ℕ) : Prop :=
  let S := D.schurData.block.polynomialSchurSeries
  (∃ hleft : S.LeftPivot,
      S.active.coeff 0 * S.offDiag.coeff n =
          S.offDiag.coeff 0 * S.active.coeff n ∧
        (S.active.coeff 0)^2 * S.kernel.coeff n =
          (S.offDiag.coeff 0)^2 * S.active.coeff n) ∨
    (∃ hright : S.RightAxisPivot,
      S.active.coeff n = 0 ∧ S.offDiag.coeff n = 0)

namespace AdaptiveAlignedRightRecenteredRankOneSchurChartData

/-- A tangential coefficient of the chosen aligned clock lies on the raw
constant rank-one ray.  This is the source-safe form of Schur tangency. -/
theorem rawSchurRayAtOrder_of_clockTangential
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (D : AdaptiveAlignedRightRecenteredRankOneSchurChartData B)
    (n : ℕ)
    (htan :
      D.clock.series.offDiag.coeff n = 0 ∧
        D.clock.series.kernel.coeff n = 0) :
    HasAdaptiveAlignedRawSchurRayAtOrder D n := by
  let E := D.schurData
  let S := E.block.polynomialSchurSeries
  generalize hp : E.chosenPivot = p
  cases p with
  | left hleft =>
      left
      refine ⟨hleft, ?_⟩
      have htan' :
          (S.alignLeft hleft).offDiag.coeff n = 0 ∧
            (S.alignLeft hleft).kernel.coeff n = 0 := by
        simpa [AdaptiveAlignedRightRecenteredRankOneSchurChartData.clock,
          AdaptiveAlignedExactFourBlockSchurData.chosenClock, E, S, hp] using htan
      exact
        S.rawRayAtOrder_of_alignLeft_tangential
          hleft n htan'.1 htan'.2
  | right hright =>
      right
      refine ⟨hright, ?_⟩
      have htan' :
          (S.alignRight hright).offDiag.coeff n = 0 ∧
            (S.alignRight hright).kernel.coeff n = 0 := by
        simpa [AdaptiveAlignedRightRecenteredRankOneSchurChartData.clock,
          AdaptiveAlignedExactFourBlockSchurData.chosenClock, E, S, hp] using htan
      exact
        S.rawRayAtOrder_of_alignRight_tangential
          hright n htan'.1 htan'.2

end AdaptiveAlignedRightRecenteredRankOneSchurChartData

namespace AdaptiveAlignedSmithRankOneClosingSourceCarrier

/-- Any Schur-tangential order of the closing carrier has a source-safe raw
ray certificate on the honest chart that generated the clock. -/
theorem rawSchurRayAtOrder_of_schurTangential
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (n : ℕ)
    (htan : C.IsClosingClockSchurTangentialOrder n) :
    HasAdaptiveAlignedRawSchurRayAtOrder C.chartData n := by
  exact C.chartData.rawSchurRayAtOrder_of_clockTangential n htan

/-- Every parameter order strictly below the exact determinant-closing defect
lies on the same source-safe raw Schur ray.  This is stronger than the
first-actual-layer statement: it packages the entire preclosing Schur prefix
without dividing in the source polynomial ring. -/
theorem rawSchurRayAtOrder_of_lt_defect
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    {n : ℕ}
    (hn : n < B.aligned.endpoint.defect) :
    HasAdaptiveAlignedRawSchurRayAtOrder C.chartData n := by
  exact
    C.rawSchurRayAtOrder_of_schurTangential
      n (C.schurTangentialOrder_of_lt_defect hn)

/-- Compact whole-prefix form used by the final local source-kernel adapter. -/
def HasAdaptiveAlignedRawSchurRayPrefix
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) : Prop :=
  ∀ n : ℕ,
    n < B.aligned.endpoint.defect →
      HasAdaptiveAlignedRawSchurRayAtOrder C.chartData n

/-- The exact closing carrier automatically carries the raw-ray certificate
at every preclosing order. -/
theorem rawSchurRayPrefix
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B) :
    HasAdaptiveAlignedRawSchurRayPrefix C := by
  intro n hn
  exact C.rawSchurRayAtOrder_of_lt_defect hn

/-- In particular the genuine first actual source layer in the preclosing
branch lies on the raw special-fibre Schur ray. -/
theorem firstActualLayer_rawSchurRay_of_lt_defect
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint (K := K) degreeCap}
    (C : AdaptiveAlignedSmithRankOneClosingSourceCarrier B)
    (hpre : C.firstActualLayerOrder < B.aligned.endpoint.defect) :
    HasAdaptiveAlignedRawSchurRayAtOrder
      C.chartData C.firstActualLayerOrder := by
  exact
    C.rawSchurRayAtOrder_of_schurTangential
      C.firstActualLayerOrder
      (C.firstActualLayer_schurTangential_of_lt_defect hpre)

end AdaptiveAlignedSmithRankOneClosingSourceCarrier

end

end HC4.Valuation
