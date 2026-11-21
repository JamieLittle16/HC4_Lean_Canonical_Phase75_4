import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectTerminalFrontier
import HC4.Newton.SingularBoundaryRankSplit

/-!
# A18.5.94: unconditional zero-defect terminal boundary frontier

A18.5.88 already places the singular maximal nonlinear ordinary top face and
the canonical Smith frontier on the same represented zero-clock terminal.
A18.5.92--93 remove the final artificial torus-balance hypothesis from the
Newton boundary extraction.

Consequently the actual zero-defect terminal now exposes, unconditionally,
either a genuine rank-three coordinate-facet vertex or a codimension-two
coordinate-boundary vertex.  This is the exact geometry required by the two
remaining terminal endpoint consumers.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry

/-- Balance-free exposed singular nonlinear vertex of the actual represented
zero-defect terminal top face. -/
noncomputable def terminalExposedSingularBoundaryVertex
    (RR : RepairRanking)
    (E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K))
    (complexity : ℕ) :
    ExposedSingularNonlinearBoundaryVertexData
      (E.terminalSingularTopFace RR complexity).face := by
  let D := E.terminalSingularTopFace RR complexity
  exact exposedSingularNonlinearBoundaryVertex
    D.face D.face_ne_zero D.hessian_zero
    (E.terminalSingularTopFace_support_degree_ge_three RR complexity)

/-- **Unconditional zero-clock boundary split.**

No `HasBalancedMvSupport` hypothesis remains: the represented terminal top
face itself supplies a singular nonlinear exposed vertex, which is either
rank three on one coordinate facet or lies on a codimension-two coordinate
boundary. -/
theorem terminalExposedBoundary_rankThreeFacet_or_codimensionTwo
    (RR : RepairRanking)
    (E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K))
    (complexity : ℕ) :
    (∃ facet : ToricFacet,
        MvRankThreeOnFacet facet
          (E.terminalExposedSingularBoundaryVertex RR complexity).exponent) ∨
      MvExponentOnCodimensionTwoBoundary
        (E.terminalExposedSingularBoundaryVertex RR complexity).exponent :=
  (E.terminalExposedSingularBoundaryVertex RR complexity).rankThreeFacet_or_codimensionTwo

end AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry

end

end HC4.Valuation
