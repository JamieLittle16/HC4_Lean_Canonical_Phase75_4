
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFinalSeamSourceSpread
import Mathlib.Tactic

/-!
# G11: a canonical simple axis-gradient pivot

The right-recentered final seam has determinant-one Hessian.  Evaluating at the
collision origin therefore gives an invertible 4 x 4 Hessian matrix, so row
zero contains a nonzero entry.  Every axis-gradient component already vanishes
at the origin.  A nonzero row-zero Hessian entry is exactly the statement that
the corresponding axis-gradient component has a simple root there.

Thus every final seam carries one canonical first-order pivot component.  The
same component also vanishes at the opposite collision endpoint by G5.

This is an unconditional local datum intended for the later one-zero/two-zero
normalisation.  It uses no progress or terminality hypothesis.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

structure FinalSeamSimpleAxisPivot
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) where
  index : Fin 4
  originHessian_ne_zero :
    T.finalSeamOriginHessian (0 : Fin 4) index ≠ 0
  exactOrderOne :
    HasExactPolynomialInitialOrder
      (T.finalSeamAxisGradientComponent index) 1
  origin_zero :
    Polynomial.eval 0 (T.finalSeamAxisGradientComponent index) = 0
  opposite_zero :
    Polynomial.eval (-1 : K) (T.finalSeamAxisGradientComponent index) = 0

/-- Determinant one produces an actual simple longitudinal-axis gradient
pivot. -/
theorem finalSeamSimpleAxisPivot
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    Nonempty T.FinalSeamSimpleAxisPivot := by
  let H := T.finalSeamOriginHessian
  have hdet : H.det ≠ 0 := by
    rw [T.finalSeamOriginHessian_det_one]
    exact one_ne_zero
  rcases matrix4_det_ne_zero_row_exists_entry H hdet (0 : Fin 4) with
    ⟨j, hj⟩
  refine ⟨{
    index := j
    originHessian_ne_zero := hj
    exactOrderOne :=
      T.finalSeamAxisGradientComponent_exactOrder_one_of_originEntry_ne_zero
        j hj
    origin_zero := T.finalSeamAxisGradientComponent_eval_zero j
    opposite_zero := T.finalSeamAxisGradientComponent_eval_neg_one j
  }⟩

/-- Equivalent coefficient-facing form of the simple pivot: its first
longitudinal coefficient is nonzero. -/
theorem FinalSeamSimpleAxisPivot.coeff_one_ne_zero
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (P : T.FinalSeamSimpleAxisPivot) :
    (T.finalSeamAxisGradientComponent P.index).coeff 1 ≠ 0 := by
  exact P.exactOrderOne.2

/-- The pivot still carries the universal two-endpoint factorisation from G5.
Keeping the quotient existential avoids choosing any extra geometry. -/
theorem FinalSeamSimpleAxisPivot.twoEndpointFactor
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (P : T.FinalSeamSimpleAxisPivot) :
    ∃ B : Polynomial K,
      T.finalSeamAxisGradientComponent P.index =
        (Polynomial.X * (Polynomial.X + Polynomial.C (1 : K))) * B := by
  exact T.finalSeamAxisGradientComponent_twoEndpoint_factor P.index

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData

end

end HC4.Valuation
