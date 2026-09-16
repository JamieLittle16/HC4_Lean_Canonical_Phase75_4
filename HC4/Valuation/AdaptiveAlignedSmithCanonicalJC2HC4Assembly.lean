import HC4.Valuation.AdaptiveAlignedSmithCanonicalHC4Reduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalPresentedRankThreeSpecialFiber
import HC4.Newton.TerminalAssociatedGradedEndpoint

/-!
# A19.4: current-terminal assembly for `JC2 => HC4`

The historical JC2-facing restart files isolate several closing-specific
associated-graded extraction interfaces.  A18.4.109 and A18.5.1 now give a
strictly better final interface: every normalized determinant-one collision
reaches one `AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal`, carrying
its actual represented state, exact special-fibre collision and all retained
rank-three provenance.

This file therefore states the only remaining JC2-facing extraction at that
current terminal type.  An implementation must construct an actual
`TerminalAssociatedGradedCollisionData`; it may not identify a Hessian/Schur
rank certificate with a polynomial endpoint.

Once that extraction is available, the old terminal endpoint theorem consumes
JC2, and A19.1 immediately yields determinant-one four-dimensional gradient
injectivity.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **The single remaining current-type extraction for conditional HC4.**

For every canonical complexity-zero presented terminal reached by A18.4.109,
construct an honest associated-graded polynomial collision carrying one of the
certified terminal endpoint types.  This proposition deliberately contains no
JC2 hypothesis: it is a geometric extraction problem. -/
def AdaptiveAlignedSmithCanonicalPresentedTerminalExtraction : Prop :=
  ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)},
    AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0 →
      Nonempty (TerminalAssociatedGradedCollisionData K)

/-- A completed current-terminal extraction makes every canonical presented
terminal contradictory under planar JC2. -/
theorem AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.impossible_of_JC2_of_extraction
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (hextract : AdaptiveAlignedSmithCanonicalPresentedTerminalExtraction
      (K := K))
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      canonicalAdaptiveAlignedSmithRepairRanking state 0) : False := by
  rcases hextract T with ⟨A⟩
  exact A.impossible_of_JC2 hJC2

/-- **A19.4 conditional final assembly.**

Planar JC2 plus the one honest current-terminal associated-graded extraction
implies injectivity of every four-dimensional polynomial gradient whose
Hessian determinant is one.  All collision normalization, degree bookkeeping,
Rees entry and well-founded A18 termination are discharged internally by
A19.1. -/
theorem gradient_injective_of_hessianDeterminant_one_of_JC2_of_presentedTerminalExtraction
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (hextract : AdaptiveAlignedSmithCanonicalPresentedTerminalExtraction
      (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) := by
  exact
    gradient_injective_of_hessianDeterminant_one_of_presentedTerminal_impossible
      F hdet
      (fun T => T.impossible_of_JC2_of_extraction hJC2 hextract)

/-- Collision-facing form of the same conditional implication. -/
theorem no_distinct_exactGradientCollision_of_hessianDeterminant_one_of_JC2_of_presentedTerminalExtraction
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (hextract : AdaptiveAlignedSmithCanonicalPresentedTerminalExtraction
      (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    ∀ p q : Fin 4 → K,
      p ≠ q → ¬ HasExactGradientCollision F p q := by
  intro p q hpq hcoll
  exact hpq
    (exactGradientCollision_eq_of_injective
      F p q
      (gradient_injective_of_hessianDeterminant_one_of_JC2_of_presentedTerminalExtraction
        hJC2 hextract F hdet)
      hcoll)

end

end HC4.Valuation
