import HC4.Newton.PreterminalFirstDeparture
import HC4.Newton.FiniteRepairTermination
import HC4.Newton.RankOneRepairProgress
import Mathlib.Tactic

/-!
# Mixed departure adapter

Phase 93.20 proves the exact preterminal dichotomy

    P_VV = 0

and either

    P_UV != 0,  det Hess_(U,V) P = -(P_UV)^2 != 0,

or

    P_UV = 0.

This file connects that dichotomy to the already-green abstract repair
measure without introducing a second termination system.

A genuine mixed pivot is interpreted as a rank promotion

    rank 1  ->  rank 2

at unchanged finite complexity.  By the existing definition of
`RepairProgress`, this is a strict repair step.

The complementary no-mixed-curvature branch remains explicitly
`IsPreterminalAffineSeparatedChannel`.

Thus the first preterminal departure is packaged exactly as

    mixed repair progress  OR  affine/separated.

This is the thin adapter requested by the restart audit.  The file does not
claim that every global restart has already been constructed; that is the
next well-founded assembly step.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- Rank-one repair state at a specified finite complexity. -/
def preterminalRankOneRepairState
    (complexity : ℕ) : RepairState where
  rank := 1
  complexity := complexity
  rank_pos := by omega
  rank_le_three := by omega

/-- Rank-two repair state reached by a genuine preterminal mixed pivot. -/
def preterminalRankTwoRepairState
    (complexity : ℕ) : RepairState where
  rank := 2
  complexity := complexity
  rank_pos := by omega
  rank_le_three := by omega

@[simp] theorem preterminalRankOneRepairState_rank
    (complexity : ℕ) :
    (preterminalRankOneRepairState complexity).rank = 1 := rfl

@[simp] theorem preterminalRankTwoRepairState_rank
    (complexity : ℕ) :
    (preterminalRankTwoRepairState complexity).rank = 2 := rfl

@[simp] theorem preterminalRankOneRepairState_complexity
    (complexity : ℕ) :
    (preterminalRankOneRepairState complexity).complexity =
      complexity := rfl

@[simp] theorem preterminalRankTwoRepairState_complexity
    (complexity : ℕ) :
    (preterminalRankTwoRepairState complexity).complexity =
      complexity := rfl

/-- A rank-one to rank-two promotion at fixed complexity is strict
`RepairProgress`. -/
theorem preterminal_rankOne_to_rankTwo_repairProgress
    (complexity : ℕ) :
    RepairProgress
      (preterminalRankOneRepairState complexity)
      (preterminalRankTwoRepairState complexity) := by
  unfold RepairProgress
  right
  constructor
  · rfl
  · norm_num [preterminalRankOneRepairState,
      preterminalRankTwoRepairState]

/-- The genuine mixed branch carries both the exact negative-square source
certificate from Phase 93.20 and a strict step in the existing repair
relation. -/
theorem preterminal_mixedPivot_matches_repairProgress
    (b : K)
    (hb : b ≠ 0)
    (U V : σ)
    (P : MvPolynomial σ K)
    (complexity : ℕ)
    (hsource :
      preterminalSchurLinearSource b V P = 0)
    (hmixed :
      directionalMixedDerivative U V P ≠ 0) :
    IsPreterminalMixedPivotChannel U V P ∧
      RepairProgress
        (preterminalRankOneRepairState complexity)
        (preterminalRankTwoRepairState complexity) := by
  constructor
  · exact
      (preterminal_mixedPivot_exact_source
        b hb U V P hsource hmixed).1
  · exact
      preterminal_rankOne_to_rankTwo_repairProgress
        complexity

/-- The adapter also retains the exact determinant source needed by any
later local rank-two theorem. -/
theorem preterminal_mixedPivot_matches_repairProgress_with_source
    (b : K)
    (hb : b ≠ 0)
    (U V : σ)
    (P : MvPolynomial σ K)
    (complexity : ℕ)
    (hsource :
      preterminalSchurLinearSource b V P = 0)
    (hmixed :
      directionalMixedDerivative U V P ≠ 0) :
    RepairProgress
        (preterminalRankOneRepairState complexity)
        (preterminalRankTwoRepairState complexity) ∧
      binaryDirectionalHessianDet U V P =
        -(directionalMixedDerivative U V P)^2 ∧
      binaryDirectionalHessianDet U V P ≠ 0 := by
  refine
    ⟨preterminal_rankOne_to_rankTwo_repairProgress
        complexity,
     ?_,
     ?_⟩
  · exact
      preterminal_binaryDet_eq_neg_sq
        b hb U V P hsource
  · exact
      preterminal_binaryDet_ne_zero_of_mixed
        b hb U V P hsource hmixed

/-- **Mixed-departure adapter dichotomy.**
Every preterminal first departure either enters the existing strict repair
relation by rank promotion, or is in the affine/separated channel. -/
theorem preterminal_departure_repairProgress_or_affineSeparated
    (b : K)
    (hb : b ≠ 0)
    (U V : σ)
    (P : MvPolynomial σ K)
    (complexity : ℕ)
    (hsource :
      preterminalSchurLinearSource b V P = 0) :
    (IsPreterminalMixedPivotChannel U V P ∧
      RepairProgress
        (preterminalRankOneRepairState complexity)
        (preterminalRankTwoRepairState complexity)) ∨
      IsPreterminalAffineSeparatedChannel U V P := by
  rcases
      preterminal_departure_dichotomy
        b hb U V P hsource with
    hmixed | haffine
  · left
    refine ⟨hmixed, ?_⟩
    exact
      preterminal_rankOne_to_rankTwo_repairProgress
        complexity
  · exact Or.inr haffine

/-- The mixed adapter strictly lowers the existing numeric repair measure.
This is proved directly from the already-defined measure, so no extra
termination measure is introduced. -/
theorem preterminal_mixedPivot_strictly_lowers_repairMeasure
    (complexity : ℕ) :
    (preterminalRankTwoRepairState complexity).measure <
      (preterminalRankOneRepairState complexity).measure := by
  unfold RepairState.measure
  unfold RepairState.rankDefect
  simp [preterminalRankOneRepairState,
    preterminalRankTwoRepairState]

/-- **Well-founded mixed-departure interface.**
At a preterminal first departure, either the branch is already in the
explicit affine/separated channel, or the mixed branch is a genuine repair
step which strictly lowers the *existing* finite repair measure.

This is the packaged form consumed by the global restart assembly: it does
not introduce a new measure and does not ask that assembly to reconstruct
the local rank-one-to-rank-two argument. -/
theorem preterminal_departure_strictRepair_or_affineSeparated
    (b : K)
    (hb : b ≠ 0)
    (U V : σ)
    (P : MvPolynomial σ K)
    (complexity : ℕ)
    (hsource :
      preterminalSchurLinearSource b V P = 0) :
    (IsPreterminalMixedPivotChannel U V P ∧
      RepairProgress
        (preterminalRankOneRepairState complexity)
        (preterminalRankTwoRepairState complexity) ∧
      (preterminalRankTwoRepairState complexity).measure <
        (preterminalRankOneRepairState complexity).measure) ∨
      IsPreterminalAffineSeparatedChannel U V P := by
  rcases
      preterminal_departure_repairProgress_or_affineSeparated
        b hb U V P complexity hsource with
    hmixed | haffine
  · left
    refine ⟨hmixed.1, hmixed.2, ?_⟩
    exact repairState_measure_lt_of_progress hmixed.2
  · exact Or.inr haffine

/-- Source-preserving version of the well-founded mixed-departure interface.
In the nonterminal branch it records, simultaneously,

* strict `RepairProgress`;
* the exact negative-square binary Hessian identity;
* nonvanishing of that determinant source; and
* strict decrease of the existing repair measure.

Thus every algebraic datum needed by a later rank-two restart theorem is
available from one first-departure call. -/
theorem preterminal_departure_strictRepair_with_source_or_affineSeparated
    (b : K)
    (hb : b ≠ 0)
    (U V : σ)
    (P : MvPolynomial σ K)
    (complexity : ℕ)
    (hsource :
      preterminalSchurLinearSource b V P = 0) :
    (RepairProgress
        (preterminalRankOneRepairState complexity)
        (preterminalRankTwoRepairState complexity) ∧
      binaryDirectionalHessianDet U V P =
        -(directionalMixedDerivative U V P)^2 ∧
      binaryDirectionalHessianDet U V P ≠ 0 ∧
      (preterminalRankTwoRepairState complexity).measure <
        (preterminalRankOneRepairState complexity).measure) ∨
      IsPreterminalAffineSeparatedChannel U V P := by
  rcases
      preterminal_departure_dichotomy
        b hb U V P hsource with
    hmixed | haffine
  · left
    have hprogress :
        RepairProgress
          (preterminalRankOneRepairState complexity)
          (preterminalRankTwoRepairState complexity) :=
      preterminal_rankOne_to_rankTwo_repairProgress complexity
    refine ⟨hprogress, ?_, ?_, ?_⟩
    · exact preterminal_binaryDet_eq_neg_sq b hb U V P hsource
    · exact hmixed.2.2
    · exact repairState_measure_lt_of_progress hprogress
  · exact Or.inr haffine


/-! ## Exact rank-promotion measure drop -/

/-- The canonical rank-one to rank-two promotion at fixed complexity lowers
the existing repair measure by exactly one.  This is stronger than the
strict inequality used by termination and is convenient when assembling a
global lexicographic restart bound. -/
theorem preterminal_rankOne_to_rankTwo_measure_drop_exact
    (complexity : ℕ) :
    (preterminalRankTwoRepairState complexity).measure + 1 =
      (preterminalRankOneRepairState complexity).measure := by
  simp [RepairState.measure, RepairState.rankDefect,
    preterminalRankOneRepairState, preterminalRankTwoRepairState]



/-! ## Canonical repair-state compatibility -/

/-- The preterminal adapter's rank-one state is definitionally the same
state as the canonical rank-one repair state. -/
@[simp] theorem preterminalRankOneRepairState_eq_rankOneRepairState
    (complexity : ℕ) :
    preterminalRankOneRepairState complexity =
      rankOneRepairState complexity := by
  rfl

/-- Likewise for active rank two.  Thus the Smith entrance and the
preterminal mixed-departure adapter use one and the same repair state space,
not merely isomorphic copies. -/
@[simp] theorem preterminalRankTwoRepairState_eq_rankTwoRepairState
    (complexity : ℕ) :
    preterminalRankTwoRepairState complexity =
      rankTwoRepairState complexity := by
  rfl

/-- Canonical-state form of the well-founded mixed-departure interface. -/
theorem preterminal_departure_canonicalStrictRepair_or_affineSeparated
    (b : K)
    (hb : b ≠ 0)
    (U V : σ)
    (P : MvPolynomial σ K)
    (complexity : ℕ)
    (hsource :
      preterminalSchurLinearSource b V P = 0) :
    (IsPreterminalMixedPivotChannel U V P ∧
      RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∧
      (rankTwoRepairState complexity).measure <
        (rankOneRepairState complexity).measure) ∨
      IsPreterminalAffineSeparatedChannel U V P := by
  simpa using
    preterminal_departure_strictRepair_or_affineSeparated
      b hb U V P complexity hsource

/-- Source-preserving canonical-state version.  This is the form a global
restart theorem can consume without translating between local state
constructors. -/
theorem preterminal_departure_canonicalStrictRepair_with_source_or_affineSeparated
    (b : K)
    (hb : b ≠ 0)
    (U V : σ)
    (P : MvPolynomial σ K)
    (complexity : ℕ)
    (hsource :
      preterminalSchurLinearSource b V P = 0) :
    (RepairProgress
        (rankOneRepairState complexity)
        (rankTwoRepairState complexity) ∧
      binaryDirectionalHessianDet U V P =
        -(directionalMixedDerivative U V P)^2 ∧
      binaryDirectionalHessianDet U V P ≠ 0 ∧
      (rankTwoRepairState complexity).measure <
        (rankOneRepairState complexity).measure) ∨
      IsPreterminalAffineSeparatedChannel U V P := by
  simpa using
    preterminal_departure_strictRepair_with_source_or_affineSeparated
      b hb U V P complexity hsource


end

end HC4.Newton
