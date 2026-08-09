import HC4.Newton.RankOneRepairProgress
import HC4.Newton.RankTwoHomogeneousPacketClassification
import Mathlib.Tactic

/-!
# Rank-two local terminal certificate

The determinant-zero rank-two Schur branch is already locally rigid.

Phase 90 produces the first nonzero binary Schur entry and Phase 91 proves
that a nonzero determinant-zero entry has one of three homogeneous normal
forms:

* a coefficientwise one-linear-form power;
* a pure left-axis packet;
* a pure right-axis packet.

This file names that conclusion as a terminal certificate for the finite
repair argument.  It is important not to manufacture a rank-two to
rank-three transition here: under the hypotheses of the Phase 91 theorem,
the rank-two branch is already classified.

The remaining global question is instead what an actual *nondegenerate*
rank-two re-entry event does to the next Rees/Schur stage.
-/

namespace HC4.Newton

noncomputable section

variable {σ K : Type*} [Field K]

/-- Local terminal certificate for the determinant-zero homogeneous
rank-two branch. -/
def HasRigidRankTwoTerminal
    (q : BinarySchurBlock K)
    (i j : σ)
    (n : ℕ)
    (F : MvPolynomial σ K) : Prop :=
  HasRankTwoHomogeneousPacketClassification q i j n F

/-- The full Phase 91 hypotheses produce the local rank-two terminal
certificate. -/
theorem hasRigidRankTwoTerminal_of_schurEntry
    [CharZero K]
    (q : BinarySchurBlock K)
    (hdet : q.detCore = 0)
    (hnz : q.Nonzero)
    {i j : σ}
    (hij : i ≠ j)
    (n mLeft mRight : ℕ)
    (F : MvPolynomial σ K)
    (hexactF : HasExactTransverseDegree i j n F)
    (hmLeftPos : 0 < mLeft)
    (hmRightPos : 0 < mRight)
    (hexactLeft :
      HasExactTransverseDegree i j mLeft
        (binaryDirectionalDeriv (-q.b) q.a i j F))
    (hexactRight :
      HasExactTransverseDegree i j mRight
        (binaryDirectionalDeriv (1 : K) 0 i j F))
    (hleftKernel :
      q.LeftPivot -> HasLeftPivotHessianKernel q i j F)
    (hrightKernel :
      q.RightAxisPivot -> HasRightAxisHessianKernel i j F) :
    HasRigidRankTwoTerminal q i j n F := by
  exact
    rankTwoHomogeneousPacketClassification
      q hdet hnz hij n mLeft mRight F
      hexactF hmLeftPos hmRightPos
      hexactLeft hexactRight hleftKernel hrightKernel

/-- Expanded terminal alternative: a rigid rank-two terminal certificate
is exactly one of the three Phase 91 normal forms. -/
theorem rigidRankTwoTerminal_cases
    {q : BinarySchurBlock K}
    {i j : σ}
    {n : ℕ}
    {F : MvPolynomial σ K}
    (hterminal : HasRigidRankTwoTerminal q i j n F) :
    (q.LeftPivot ∧ q.b ≠ 0 ∧
      HasLinearPowerTransverseNormalForm
        (-q.b) q.a i j n F) ∨
    (q.LeftPivot ∧ q.b = 0 ∧
      HasPureLeftAxisTransverseDegree i j n F) ∨
    (q.RightAxisPivot ∧
      HasPureRightAxisTransverseDegree i j n F) := by
  exact hterminal


/-! ## Rank-two terminal-or-progress bridge -/

/-- Restart-facing local outcome for a nonzero rank-two binary Schur entry:
either the determinant-zero branch is already rigid, or the determinant is
nonzero and the active rank makes the canonical `2 -> 3` repair step. -/
def HasRankTwoTerminalOrStrictRepair
    (q : BinarySchurBlock K)
    (i j : σ)
    (n : ℕ)
    (F : MvPolynomial σ K)
    (complexity : ℕ) : Prop :=
  HasRigidRankTwoTerminal q i j n F ∨
    (q.detCore ≠ 0 ∧
      RepairProgress
        (rankTwoRepairState complexity)
        (rankThreeRepairState complexity) ∧
      (rankThreeRepairState complexity).measure <
        (rankTwoRepairState complexity).measure)

/-- **Rank-two local repair dichotomy.**

Under exactly the hypotheses already used to classify the determinant-zero
rank-two Schur entry, no third local branch exists.  If `detCore = 0`, the
existing Phase 91 theorem gives the rigid terminal normal form.  If
`detCore != 0`, the entry is nondegenerate and is packaged as the canonical
rank-two to rank-three strict repair step. -/
theorem rankTwoSchurEntry_terminal_or_strictRepair
    [CharZero K]
    (q : BinarySchurBlock K)
    (hnz : q.Nonzero)
    {i j : σ}
    (hij : i ≠ j)
    (n mLeft mRight complexity : ℕ)
    (F : MvPolynomial σ K)
    (hexactF : HasExactTransverseDegree i j n F)
    (hmLeftPos : 0 < mLeft)
    (hmRightPos : 0 < mRight)
    (hexactLeft :
      HasExactTransverseDegree i j mLeft
        (binaryDirectionalDeriv (-q.b) q.a i j F))
    (hexactRight :
      HasExactTransverseDegree i j mRight
        (binaryDirectionalDeriv (1 : K) 0 i j F))
    (hleftKernel :
      q.LeftPivot -> HasLeftPivotHessianKernel q i j F)
    (hrightKernel :
      q.RightAxisPivot -> HasRightAxisHessianKernel i j F) :
    HasRankTwoTerminalOrStrictRepair
      q i j n F complexity := by
  by_cases hdet : q.detCore = 0
  · left
    exact
      hasRigidRankTwoTerminal_of_schurEntry
        q hdet hnz hij n mLeft mRight F
        hexactF hmLeftPos hmRightPos
        hexactLeft hexactRight hleftKernel hrightKernel
  · right
    have hprogress :
        RepairProgress
          (rankTwoRepairState complexity)
          (rankThreeRepairState complexity) :=
      rankTwo_to_rankThree_repairProgress complexity
    exact
      ⟨hdet, hprogress,
        repairState_measure_lt_of_progress hprogress⟩

/-- Stronger exhaustion form of the rank-two dichotomy.  In the
nondegenerate branch, not only is the `2 -> 3` promotion strict, but *every*
subsequent repair from rank three must lower complexity. -/
theorem rankTwoSchurEntry_terminal_or_rankThreeExhaustion
    [CharZero K]
    (q : BinarySchurBlock K)
    (hnz : q.Nonzero)
    {i j : σ}
    (hij : i ≠ j)
    (n mLeft mRight complexity : ℕ)
    (F : MvPolynomial σ K)
    (hexactF : HasExactTransverseDegree i j n F)
    (hmLeftPos : 0 < mLeft)
    (hmRightPos : 0 < mRight)
    (hexactLeft :
      HasExactTransverseDegree i j mLeft
        (binaryDirectionalDeriv (-q.b) q.a i j F))
    (hexactRight :
      HasExactTransverseDegree i j mRight
        (binaryDirectionalDeriv (1 : K) 0 i j F))
    (hleftKernel :
      q.LeftPivot -> HasLeftPivotHessianKernel q i j F)
    (hrightKernel :
      q.RightAxisPivot -> HasRightAxisHessianKernel i j F) :
    HasRigidRankTwoTerminal q i j n F ∨
      (q.detCore ≠ 0 ∧
        RepairProgress
          (rankTwoRepairState complexity)
          (rankThreeRepairState complexity) ∧
        (rankThreeRepairState complexity).measure <
          (rankTwoRepairState complexity).measure ∧
        ∀ t : RepairState,
          RepairProgress
              (rankThreeRepairState complexity) t ->
            t.complexity < complexity) := by
  rcases
      rankTwoSchurEntry_terminal_or_strictRepair
        q hnz hij n mLeft mRight complexity F
        hexactF hmLeftPos hmRightPos
        hexactLeft hexactRight
        hleftKernel hrightKernel with
    hterminal | hrepair
  · exact Or.inl hterminal
  · right
    refine ⟨hrepair.1, hrepair.2.1, hrepair.2.2, ?_⟩
    intro t hnext
    exact
      rankThree_repairProgress_forces_complexityDrop
        complexity hnext


end

end HC4.Newton
