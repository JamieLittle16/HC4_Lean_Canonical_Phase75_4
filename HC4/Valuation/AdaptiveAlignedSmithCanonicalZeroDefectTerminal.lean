import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
import Mathlib.Tactic

/-!
# A18.5.77: determinant-one entry is already at the rank-three terminal

A18.5.76 embeds a normalized determinant-one exact gradient collision as a
scale-aware state with literal raw Hessian defect `0`.  A18.4.109 supplies a
finite rank-one termination trace whose only recursive constructor has a
strictly smaller natural-valued raw defect.

Consequently that trace cannot take even one restart step: a successor would
have raw defect strictly below zero.  The initial state itself therefore
carries the complete aligned rank-three geometry, and hence the normalized
presented rank-three terminal of A18.5.1.

This is the exact entry-facing form needed by the final HC4 splice.  No new
termination measure and no repair-state argument is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry

/-- A determinant-one collision entry cannot traverse a strict raw-defect
restart.  Its A18.4.109 trace is terminal at the original state. -/
noncomputable def alignedRankThreeGeometry
    (RR : RepairRanking)
    (E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K))
    (complexity : ℕ) :
    AdaptiveAlignedSmithCanonicalAlignedRankThreeGeometry
      RR (E.toScaleAwareState complexity) complexity := by
  let T := E.rankOneTerminationTrace RR complexity
  cases T with
  | terminal geometry =>
      exact geometry
  | restart progress rawDefect_lt repair_eq tail =>
      have hfalse : False := by
        simpa using rawDefect_lt
      exact hfalse.elim

/-- **Zero-defect terminal collapse.**
The normalized determinant-one collision reaches the presented rank-three
terminal on the original scale-aware state itself. -/
noncomputable def presentedRankThreeTerminal
    (RR : RepairRanking)
    (E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K))
    (complexity : ℕ) :
    AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      RR (E.toScaleAwareState complexity) complexity :=
  (E.alignedRankThreeGeometry RR complexity).toPresentedTerminal

end AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry

end

end HC4.Valuation