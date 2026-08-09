import HC4.Newton.FiniteRepairTermination
import Mathlib.Tactic

/-!
# Rank-one packet re-entry as genuine repair progress

Phase 92.3 proves that every nonzero rank-one persistent packet has one of
two algebraic outcomes:

* discriminant zero, with explicit square/axis geometry;
* discriminant nonzero, with nonzero determinant core and trivial
  transverse kernel.

Phase 93.1 introduces the well-founded repair state

    (active rank, Rees/Newton complexity)

and declares progress when complexity drops, or when complexity is fixed
and active rank strictly increases.

This file connects those two layers for the rank-one branch.

At any fixed complexity `c`, the nondegenerate Phase 92.3 outcome is
interpreted as the concrete state transition

    (rank 1, complexity c)  -->  (rank 2, complexity c),

which is a `RepairProgress` step and therefore strictly lowers the Phase
93.1 termination measure.

The discriminant-zero branch is retained separately as its already-rigid
square/axis terminal certificate.

This is the first non-tautological bridge from the local corank
classification into the finite termination engine.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- Canonical repair state of active transverse rank one. -/
def rankOneRepairState
    (complexity : ℕ) : RepairState where
  rank := 1
  complexity := complexity
  rank_pos := by omega
  rank_le_three := by omega

/-- Canonical repair state of active transverse rank two. -/
def rankTwoRepairState
    (complexity : ℕ) : RepairState where
  rank := 2
  complexity := complexity
  rank_pos := by omega
  rank_le_three := by omega

/-- Canonical repair state of active transverse rank three. -/
def rankThreeRepairState
    (complexity : ℕ) : RepairState where
  rank := 3
  complexity := complexity
  rank_pos := by omega
  rank_le_three := by omega

/-- The rigid discriminant-zero outcome from Phase 92.3. -/
def HasRigidRankOnePacket
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K) : Prop :=
  rankOnePacketDiscriminant x y z D F = 0 ∧
    (((rankOnePacketQuadraticBlock x y z D F).LeftPivot ∧
      (∀ Y Z : K,
        (rankOnePacketQuadraticBlock x y z D F).a *
            (rankOnePacketQuadraticBlock x y z D F).quadratic Y Z =
          ((rankOnePacketQuadraticBlock x y z D F).a * Y +
            (rankOnePacketQuadraticBlock x y z D F).b * Z) ^ 2)) ∨
    ((rankOnePacketQuadraticBlock x y z D F).RightAxisPivot ∧
      (∀ Y Z : K,
        (rankOnePacketQuadraticBlock x y z D F).quadratic Y Z =
          (rankOnePacketQuadraticBlock x y z D F).c * Z * Z)))

/-- The genuinely rank-two/nondegenerate outcome from Phase 92.3. -/
def HasRankTwoPacketEscalation
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K) : Prop :=
  rankOnePacketDiscriminant x y z D F ≠ 0 ∧
    (rankOnePacketQuadraticBlock x y z D F).detCore ≠ 0 ∧
    (rankOnePacketQuadraticBlock x y z D F).HasTrivialKernel

/-- Raising active rank from one to two at fixed complexity is genuine
`RepairProgress`. -/
theorem rankOne_to_rankTwo_repairProgress
    (complexity : ℕ) :
    RepairProgress
      (rankOneRepairState complexity)
      (rankTwoRepairState complexity) := by
  right
  constructor
  · rfl
  · change 1 < 2
    omega

/-- Likewise, raising active rank from two to three at fixed complexity is
a genuine progress step.  This is recorded here for the next rank-two
bridge. -/
theorem rankTwo_to_rankThree_repairProgress
    (complexity : ℕ) :
    RepairProgress
      (rankTwoRepairState complexity)
      (rankThreeRepairState complexity) := by
  right
  constructor
  · rfl
  · change 2 < 3
    omega

/-- The rank-one to rank-two transition lowers the termination measure by
exactly one. -/
theorem rankTwo_measure_succ_eq_rankOne_measure
    (complexity : ℕ) :
    (rankTwoRepairState complexity).measure + 1 =
      (rankOneRepairState complexity).measure := by
  simp [RepairState.measure, RepairState.rankDefect,
    rankOneRepairState, rankTwoRepairState]

/-- The rank-two to rank-three transition likewise lowers the termination
measure by exactly one. -/
theorem rankThree_measure_succ_eq_rankTwo_measure
    (complexity : ℕ) :
    (rankThreeRepairState complexity).measure + 1 =
      (rankTwoRepairState complexity).measure := by
  simp [RepairState.measure, RepairState.rankDefect,
    rankTwoRepairState, rankThreeRepairState]

/-- Phase 92.3's re-entry proposition is exactly the disjunction between
the rigid rank-one packet and the rank-two escalation certificate. -/
theorem rankOnePacketReentry_iff_rigid_or_escalates
    (x y z : σ)
    (D : ℕ)
    (F : MvPolynomial σ K) :
    HasRankOnePacketReentry x y z D F ↔
      HasRigidRankOnePacket x y z D F ∨
      HasRankTwoPacketEscalation x y z D F := by
  rfl

/-- **Rank-one local classification feeds the termination engine.**
A nonzero persistent packet is either already in the rigid
discriminant-zero geometry, or its nondegenerate transverse quadratic
certifies a genuine rank-one to rank-two repair step at the same
complexity. -/
theorem rankOnePersistentPacket_rigid_or_rankTwoProgress
    [CharZero K]
    {x y z : σ}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    {D complexity : ℕ}
    {F : MvPolynomial σ K}
    (hpacket : HasRankOnePersistentPacketSupport x y z D F)
    (hF : F ≠ 0) :
    HasRigidRankOnePacket x y z D F ∨
      (HasRankTwoPacketEscalation x y z D F ∧
        RepairProgress
          (rankOneRepairState complexity)
          (rankTwoRepairState complexity)) := by
  have hreentry :
      HasRankOnePacketReentry x y z D F :=
    rankOnePersistentPacket_reentry
      hxy hxz hyz hpacket hF
  have hcases :
      HasRigidRankOnePacket x y z D F ∨
        HasRankTwoPacketEscalation x y z D F :=
    (rankOnePacketReentry_iff_rigid_or_escalates
      x y z D F).1 hreentry
  rcases hcases with hrigid | hesc
  · exact Or.inl hrigid
  · exact Or.inr
      ⟨hesc, rankOne_to_rankTwo_repairProgress complexity⟩

/-- In the escalating branch, the Phase 93.1 measure decreases
immediately. -/
theorem rankOnePersistentPacket_escalation_measure_lt
    [CharZero K]
    {x y z : σ}
    (hxy : x ≠ y)
    (hxz : x ≠ z)
    (hyz : y ≠ z)
    {D complexity : ℕ}
    {F : MvPolynomial σ K}
    (hpacket : HasRankOnePersistentPacketSupport x y z D F)
    (hF : F ≠ 0)
    (hnotRigid : ¬ HasRigidRankOnePacket x y z D F) :
    (rankTwoRepairState complexity).measure <
      (rankOneRepairState complexity).measure := by
  rcases rankOnePersistentPacket_rigid_or_rankTwoProgress
      hxy hxz hyz hpacket hF with hrigid | hprogress
  · exact False.elim (hnotRigid hrigid)
  · exact repairState_measure_lt_of_progress hprogress.2


/-! ## Canonical rank-ladder exhaustion -/

/-- From canonical active rank two, every progressing repair either lowers
complexity immediately or, at unchanged complexity, is forced all the way
to the unique remaining rank `3`. -/
theorem rankTwo_repairProgress_complexityDrop_or_rankThree
    (complexity : ℕ)
    {t : RepairState}
    (hprogress :
      RepairProgress (rankTwoRepairState complexity) t) :
    t.complexity < complexity ∨
      (t.complexity = complexity ∧ t.rank = 3) := by
  unfold RepairProgress at hprogress
  rcases hprogress with hdrop | ⟨hsame, hrank⟩
  · exact Or.inl (by
      simpa [rankTwoRepairState] using hdrop)
  · right
    constructor
    · simpa [rankTwoRepairState] using hsame
    · have hrank' : 2 < t.rank := by
        simpa [rankTwoRepairState] using hrank
      have hle := t.rank_le_three
      omega

/-- Once canonical active rank three has been reached, rank promotion is
impossible.  Hence every further genuine repair must strictly lower the
finite Rees/Newton complexity. -/
theorem rankThree_repairProgress_forces_complexityDrop
    (complexity : ℕ)
    {t : RepairState}
    (hprogress :
      RepairProgress (rankThreeRepairState complexity) t) :
    t.complexity < complexity := by
  unfold RepairProgress at hprogress
  rcases hprogress with hdrop | ⟨_hsame, hrank⟩
  · simpa [rankThreeRepairState] using hdrop
  · have hrank' : 3 < t.rank := by
      simpa [rankThreeRepairState] using hrank
    have hle := t.rank_le_three
    omega

/-- The two possible fixed-complexity promotions, `1 -> 2 -> 3`, consume
exactly two units of the repair measure. -/
theorem rankThree_measure_add_two_eq_rankOne_measure
    (complexity : ℕ) :
    (rankThreeRepairState complexity).measure + 2 =
      (rankOneRepairState complexity).measure := by
  have h12 :=
    rankTwo_measure_succ_eq_rankOne_measure complexity
  have h23 :=
    rankThree_measure_succ_eq_rankTwo_measure complexity
  omega

/-- Packaged canonical exhaustion statement: the rank ladder contains only
the two fixed-complexity promotions `1 -> 2 -> 3`, and after rank three every
additional repair lowers complexity. -/
theorem canonical_rankLadder_exhaustion
    (complexity : ℕ) :
    RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∧
      RepairProgress
        (rankTwoRepairState complexity)
        (rankThreeRepairState complexity) ∧
      (∀ t : RepairState,
        RepairProgress (rankThreeRepairState complexity) t ->
          t.complexity < complexity) := by
  refine
    ⟨rankOne_to_rankTwo_repairProgress complexity,
      rankTwo_to_rankThree_repairProgress complexity,
      ?_⟩
  intro t hprogress
  exact
    rankThree_repairProgress_forces_complexityDrop
      complexity hprogress


end

end HC4.Newton
