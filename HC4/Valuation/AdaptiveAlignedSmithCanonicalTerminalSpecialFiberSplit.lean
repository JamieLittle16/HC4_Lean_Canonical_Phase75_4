import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedRankThreeSpecialFiber
import HC4.Valuation.PolynomialFamilyHessianSpecialFiber
import Mathlib.Tactic

/-!
# A18.5.18: every presented rank-three terminal has one honest polynomial defect status

The primitive A18.5.3 terminal split is useful for retaining local rank-three
provenance, but the Newton consumer should not have to repeat the same Hessian
specialisation argument in every constructor.

A normalized presented terminal `T` already stores a certified pure ramified
presentation

    T.presentedState  -->  source.

Such a presentation preserves zero/nonzero status of the raw determinant
clock.  Consequently there are only two polynomial-level possibilities:

* the source clock is zero, and so is the represented terminal clock; or
* the source clock is positive, hence the represented terminal clock is
  positive, and A18.5.7 says that the *actual polynomial special fibre* of
  `T.presentedState` has zero ordinary Hessian determinant.

This is a lossless reduction.  The terminal object itself remains attached,
so all nine primitive Hessian/Schur geometries are still available after the
common polynomial singularity has been exposed.
-/

namespace HC4.Valuation

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

/-- Zero-clock terminal data, retaining both source and represented clock
identities. -/
structure ZeroSpecialFiberData
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) : Prop where
  source_zero : source.rawDefect = 0
  presented_zero : T.presentedState.rawDefect = 0

/-- Positive-clock terminal data on the actual represented polynomial. -/
structure SingularSpecialFiberData
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) : Prop where
  source_pos : 0 < source.rawDefect
  presented_pos : 0 < T.presentedState.rawDefect
  hessian_zero :
    HC4.Polynomial.hessianDeterminant T.specialFiber = 0

/-- Honest terminal special-fibre dichotomy. -/
inductive SpecialFiberDefectOutcome
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) : Prop
  | zero (data : ZeroSpecialFiberData T)
  | singular (data : SingularSpecialFiberData T)

/-- A certified pure presentation preserves zero raw defect in the forward
direction needed by the terminal split. -/
theorem presentedState_rawDefect_eq_zero_of_source
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity)
    (hzero : source.rawDefect = 0) :
    T.presentedState.rawDefect = 0 := by
  rcases T.sourcePresentation with ⟨hmove⟩
  rw [hmove.raw_eq, hzero]
  simp

/-- Conversely, zero represented clock forces zero source clock. -/
theorem source_rawDefect_eq_zero_of_presentedState
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity)
    (hzero : T.presentedState.rawDefect = 0) :
    source.rawDefect = 0 :=
  T.sourcePresentation.source_rawDefect_eq_zero_of_target hzero

/-- Presentation provenance preserves positivity of the determinant clock. -/
theorem presentedState_rawDefect_pos_of_source_pos
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity)
    (hpos : 0 < source.rawDefect) :
    0 < T.presentedState.rawDefect := by
  apply Nat.pos_of_ne_zero
  intro hzero
  have hsourceZero := T.source_rawDefect_eq_zero_of_presentedState hzero
  omega

/-- **A18.5.18 common terminal polynomial interface.**
Every normalized rank-three terminal is either genuinely zero-clock, or its
actual represented special fibre is Hessian-singular. -/
theorem specialFiberDefectOutcome
    {RR : RepairRanking}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {complexity : ℕ}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR source complexity) :
    SpecialFiberDefectOutcome T := by
  by_cases hzero : source.rawDefect = 0
  · exact .zero {
      source_zero := hzero
      presented_zero := T.presentedState_rawDefect_eq_zero_of_source hzero
    }
  · have hsourcePos : 0 < source.rawDefect := Nat.pos_of_ne_zero hzero
    have hpresentedPos : 0 < T.presentedState.rawDefect :=
      T.presentedState_rawDefect_pos_of_source_pos hsourcePos
    have hdet :=
      T.presentedState.specialFiber_hessianDeterminant_eq_zero hpresentedPos
    exact .singular {
      source_pos := hsourcePos
      presented_pos := hpresentedPos
      hessian_zero := by
        simpa [specialFiber] using hdet
    }

end AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal

/-- The well-founded A18.4.109 trace reaches the same two-way honest
polynomial endpoint: zero clock or a singular represented special fibre. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalRankOneTerminationTrace.reachedSpecialFiberDefectOutcome
    {RR : RepairRanking}
    {complexity : ℕ}
    {source : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity source) :
    AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.SpecialFiberDefectOutcome
      T.reachedPresentedRankThree.terminal :=
  T.reachedPresentedRankThree.terminal.specialFiberDefectOutcome

end

end HC4.Valuation
