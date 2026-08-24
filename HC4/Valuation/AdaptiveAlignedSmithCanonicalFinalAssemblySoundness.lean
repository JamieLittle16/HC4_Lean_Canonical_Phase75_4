import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalMacroTermination

/-!
# Final-assembly soundness guard

The final HC4 assembly must terminate on geometric information, not on the
finite `RepairState` tag alone.

`ScaleAwareAdaptiveGeometricRestartState.withRepairOnly` deliberately changes
only the repair metadata: the polynomial family, moving collision section,
Hessian-defect certificate, scale, degree bound and source complexity are all
unchanged.  Consequently every scale-aware collision state can be relabelled
as the numerically exhausted repair state `rankThreeRepairState 0`.

This file records that fact as a regression theorem.  In particular, a theorem
claiming that every scale-aware state with repair tag `rankThreeRepairState 0`
is contradictory is *equivalent* to saying that no scale-aware collision state
exists at all.  Such an endpoint theorem therefore cannot be discharged by the
repair measure; it must consume an actual geometry-carrying terminal
certificate.

The purpose of this module is to prevent the final assembly from accidentally
turning the bookkeeping-only rank ladder of A17.9 into a proof of the desired
geometric endpoint.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K] [CharZero K]

/-- There are no scale-aware exact-collision states at all.  This is the
state-level contradiction which a genuine completed global HC4 reduction
would have to establish from geometry. -/
def NoScaleAwareAdaptiveCollisionState : Prop :=
  ∀ s : ScaleAwareAdaptiveGeometricRestartState (K := K), False

/-- The apparently weaker statement that the numerically exhausted repair tag
`rankThreeRepairState 0` is impossible. -/
def ExhaustedRankThreeRepairStateImpossible : Prop :=
  ∀ s : ScaleAwareAdaptiveGeometricRestartState (K := K),
    s.repair = rankThreeRepairState 0 → False

/-- Relabelling to the exhausted repair tag preserves every geometric field of
an adaptive restart state. -/
theorem ScaleAwareAdaptiveGeometricRestartState.exhaustedRepairRelabel_geometry
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) :
    let t := s.withRepairOnly (rankThreeRepairState 0)
    t.family = s.family ∧
      t.movingSection = s.movingSection ∧
      t.rawDefect = s.rawDefect ∧
      t.scale = s.scale ∧
      t.degreeCap = s.degreeCap ∧
      t.sourceComplexity = s.sourceComplexity := by
  simp [ScaleAwareAdaptiveGeometricRestartState.withRepairOnly]

/-- **Final-assembly regression theorem.**

Because `withRepairOnly` can put the exhausted rank-three tag on *any* state
without changing its geometry, impossibility of all exhausted-tag states is
not a terminal lemma weaker than HC4-level state exclusion: it is exactly the
same proposition. -/
theorem exhaustedRankThreeRepairStateImpossible_iff_noScaleAwareAdaptiveCollisionState :
    ExhaustedRankThreeRepairStateImpossible (K := K) ↔
      NoScaleAwareAdaptiveCollisionState (K := K) := by
  constructor
  · intro hexhausted s
    let t := s.withRepairOnly (rankThreeRepairState 0)
    apply hexhausted t
    rfl
  · intro hall s _hs
    exact hall s

/-- The same issue already occurs at the rank-one entrance: since repair is
bookkeeping-only, every scale-aware state can also be relabelled as a canonical
rank-one state. -/
def AllCanonicalRankOneRepairStatesImpossible : Prop :=
  ∀ s : ScaleAwareAdaptiveGeometricRestartState (K := K),
    ∀ complexity : ℕ,
      s.repair = rankOneRepairState complexity → False

/-- Excluding every canonical rank-one-labelled state is likewise equivalent
to excluding every scale-aware collision state. -/
theorem allCanonicalRankOneRepairStatesImpossible_iff_noScaleAwareAdaptiveCollisionState :
    AllCanonicalRankOneRepairStatesImpossible (K := K) ↔
      NoScaleAwareAdaptiveCollisionState (K := K) := by
  constructor
  · intro hrankOne s
    let t := s.withRepairOnly (rankOneRepairState 0)
    apply hrankOne t 0
    rfl
  · intro hall s _complexity _hs
    exact hall s

/-- The canonical rank-three/complexity-zero repair tag has numerical measure
zero.  Therefore the abstract repair relation itself has no successor from
that tag; any genuine continuation must come from additional geometry. -/
theorem rankThreeRepairState_zero_measure :
    (rankThreeRepairState 0).measure = 0 := by
  simp [RepairState.measure, RepairState.rankDefect, rankThreeRepairState]

/-- There is no `RepairProgress` step out of the numerically exhausted repair
state.  This makes explicit where A17.9's bookkeeping recursion stops. -/
theorem not_repairProgress_rankThreeRepairState_zero
    (t : RepairState) :
    ¬ RepairProgress (rankThreeRepairState 0) t := by
  intro hprogress
  have hlt := repairState_measure_lt_of_progress hprogress
  have hzero : (rankThreeRepairState 0).measure = 0 :=
    rankThreeRepairState_zero_measure
  rw [hzero] at hlt
  exact Nat.not_lt_zero _ hlt

end

end HC4.Valuation
