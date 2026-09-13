import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectTerminal
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectTopFaceHomogeneous
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalSupportFrontier
import Mathlib.Tactic

/-!
# A18.5.88: zero-defect terminal frontier on one honest presentation

A18.5.77 shows that a normalized determinant-one collision is terminal at raw
Hessian defect zero.  The terminal presentation itself may still be a certified
ramified presentation of that state, so the final contradiction should not
silently identify two polynomial families.

Instead we work on the terminal's actual `presentedState`.  Presentation
provenance preserves the zero raw clock.  Hence that same represented state
simultaneously carries

* the genuine maximal nonlinear ordinary top face, which is nonzero,
  homogeneous and Hessian-singular; and
* the canonical Smith pole-minimal support frontier of A18.5.21.

This is the lossless zero-clock interface needed by the final finite-case
contradiction.  No toric balance, exponent line or synthetic presentation is
introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry

/-- The represented state of the zero-defect terminal still has literal raw
clock zero. -/
theorem presentedRankThreeTerminal_presentedState_rawDefect_zero
    (RR : RepairRanking)
    (E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K))
    (complexity : ℕ) :
    (E.presentedRankThreeTerminal RR complexity).presentedState.rawDefect = 0 := by
  apply (E.presentedRankThreeTerminal RR complexity).presentedState_rawDefect_eq_zero_of_source
  simp [AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry.toScaleAwareState]

/-- The actual represented zero-clock terminal has its own honest singular
maximal ordinary top face. -/
noncomputable def terminalSingularTopFace
    (RR : RepairRanking)
    (E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K))
    (complexity : ℕ) :
    AdaptiveAlignedSmithCanonicalZeroDefectSingularTopFaceData
      (E.presentedRankThreeTerminal RR complexity).presentedState :=
  (E.presentedRankThreeTerminal RR complexity).presentedState.zeroDefect_singularTopFace
    (E.presentedRankThreeTerminal_presentedState_rawDefect_zero RR complexity)

/-- The selected terminal top face is genuinely homogeneous at an attained
nonlinear degree. -/
theorem terminalSingularTopFace_homogeneous
    (RR : RepairRanking)
    (E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K))
    (complexity : ℕ) :
    (E.terminalSingularTopFace RR complexity).face.IsHomogeneous
      (E.terminalSingularTopFace RR complexity).degree :=
  (E.terminalSingularTopFace RR complexity).face_isHomogeneous

/-- Every monomial of that top face has ordinary degree at least three. -/
theorem terminalSingularTopFace_support_degree_ge_three
    (RR : RepairRanking)
    (E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K))
    (complexity : ℕ) :
    ∀ d ∈ (E.terminalSingularTopFace RR complexity).face.support,
      3 ≤ HC4.Polynomial.ordinaryDegree4 d :=
  (E.terminalSingularTopFace RR complexity).face_support_degree_ge_three

/-- The same represented terminal also retains the exact canonical Smith
support frontier.  The inferred proposition is precisely the blocker-or-
quadratic-refinement dichotomy of `specialFiber_blocker_or_quadraticRefinement`.
Keeping this as a named proof avoids any presentation change between the
singular top-face consumer and the finite Smith consumer. -/
noncomputable def terminalSupportFrontier
    (RR : RepairRanking)
    (E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K))
    (complexity : ℕ) :=
  (E.presentedRankThreeTerminal RR complexity).specialFiber_blocker_or_quadraticRefinement

end AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry

end

end HC4.Valuation
