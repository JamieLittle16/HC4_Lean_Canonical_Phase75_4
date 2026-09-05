import HC4.Valuation.AdaptiveAlignedSmithCanonicalPrimitiveRankThreeTerminal
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectTopFaceSelection
import HC4.Valuation.PolynomialFamilyHessianSpecialFiber
import Mathlib.Tactic

/-!
# A18.5.13: uniform singular polynomial carrier at a presented terminal

The actual presented endpoint has two determinant-clock regimes.

* At raw defect zero its special fibre has determinant one, so A18.5.12
  selects a genuine nonzero nonlinear maximal ordinary face with zero Hessian
  determinant.
* At positive raw defect A18.5.7 says that the actual special fibre itself has
  zero Hessian determinant.

This file packages that exhaustive split directly on the presented state.  No
terminal geometry is reinterpreted and no positive-defect nonzeroness is
asserted here; the latter must come from the retained rank-three geometry.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Singular polynomial carrier attached to a normalized presented terminal. -/
inductive AdaptiveAlignedSmithCanonicalTerminalSingularCarrier
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) : Type (u + 1)
  | zeroDefect
      (data : AdaptiveAlignedSmithCanonicalZeroDefectSingularTopFaceData
        T.presentedState)
  | positiveDefect
      (rawDefect_pos : 0 < T.presentedState.rawDefect)
      (hessian_zero :
        HC4.Polynomial.hessianDeterminant T.specialFiber = 0)

/-- Every normalized terminal supplies a singular polynomial carrier. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.singularCarrier
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) :
    AdaptiveAlignedSmithCanonicalTerminalSingularCarrier T := by
  by_cases hzero : T.presentedState.rawDefect = 0
  · exact .zeroDefect
      (T.presentedState.zeroDefect_singularTopFace hzero)
  · have hpos : 0 < T.presentedState.rawDefect := Nat.pos_of_ne_zero hzero
    exact .positiveDefect hpos (by
      simpa [AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.specialFiber]
        using T.presentedState.specialFiber_hessianDeterminant_eq_zero hpos)

/-- The well-founded A18.4.109 trace therefore reaches a presented terminal
with an honest singular polynomial carrier. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.reachedSingularCarrier
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source) :
    AdaptiveAlignedSmithCanonicalTerminalSingularCarrier
      T.reachedPresentedRankThree.terminal :=
  T.reachedPresentedRankThree.terminal.singularCarrier

end

end HC4.Valuation
