import HC4.Valuation.AdaptiveAlignedSmithCanonicalReachableHC4Reduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction
import HC4.Newton.TerminalAssociatedGradedEndpoint

/-!
# A19.7: the exact mixed reachable-terminal resolution for `JC2 => HC4`

The final terminal need not be forced through one representation.  The A18
endgame already contains unconditional polynomial contradictions, while the
terminal endpoint library contains a separate class of honest associated-
graded polynomial collisions which are contradictory under planar JC2.

For unrestricted HC4 the A19.5--6 front door needs only terminals whose raw
determinant clock is at most six.  Accordingly the remaining geometric task is
exactly this mixed resolver on that reachable frontier:

* either construct one of the already-closed A18 polynomial obstructions; or
* construct an honest `TerminalAssociatedGradedCollisionData` consumed by JC2.

No Schur/Hessian rank certificate is identified with a polynomial endpoint,
and no terminal cocharacter is manufactured.  This file only proves that a
resolver returning either *genuine* object is sufficient.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Honest alternatives which can close one current presented terminal.
The terminal remains an index of the resolver so a later producer is forced
to be constructed at the actual reached endpoint. -/
inductive AdaptiveAlignedSmithCanonicalReachableTerminalResolution
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      canonicalAdaptiveAlignedSmithRepairRanking state 0) : Type (u + 1)
  | polynomialObstruction
      (O : AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction (K := K))
  | associatedGradedCollision
      (A : TerminalAssociatedGradedCollisionData K)

/-- The sole remaining geometric producer required by the reachable reduction.
It is deliberately restricted to the clock interval that can actually arise
from the determinant-one `0 -> 6` front door. -/
def AdaptiveAlignedSmithCanonicalReachableTerminalResolutionProperty : Prop :=
  ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)},
    state.rawDefect ≤ 6 →
    ∀ T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      canonicalAdaptiveAlignedSmithRepairRanking state 0,
      Nonempty (AdaptiveAlignedSmithCanonicalReachableTerminalResolution T)

/-- Either honest terminal resolution is contradictory under planar JC2. -/
theorem AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal.impossible_of_JC2_of_reachableResolution
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (hresolve : AdaptiveAlignedSmithCanonicalReachableTerminalResolutionProperty
      (K := K))
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (hclock : state.rawDefect ≤ 6)
    (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
      canonicalAdaptiveAlignedSmithRepairRanking state 0) : False := by
  rcases hresolve hclock T with ⟨R⟩
  cases R with
  | polynomialObstruction O =>
      exact O.impossible
  | associatedGradedCollision A =>
      exact A.impossible_of_JC2 hJC2

/-- **Final reachable reduction.**

Planar JC2 plus the mixed geometric resolver on the actual seven-clock HC4
frontier implies unrestricted four-dimensional Hessian-gradient injectivity.
All normalization, degree bookkeeping, the one-time Rees entry and the only
well-founded recursion are internal to A19.6. -/
theorem gradient_injective_of_hessianDeterminant_one_of_JC2_of_reachableResolution
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (hresolve : AdaptiveAlignedSmithCanonicalReachableTerminalResolutionProperty
      (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) := by
  exact
    gradient_injective_of_hessianDeterminant_one_of_reachableTerminal_impossible
      F hdet
      (fun hclock T =>
        T.impossible_of_JC2_of_reachableResolution hJC2 hresolve hclock)

/-- The older universal associated-graded extraction is strictly stronger than
the reachable mixed resolver: if it is available, choose its honest JC2
endpoint branch. -/
theorem reachableTerminalResolution_of_presentedTerminalExtraction
    (hextract : AdaptiveAlignedSmithCanonicalPresentedTerminalExtraction
      (K := K)) :
    AdaptiveAlignedSmithCanonicalReachableTerminalResolutionProperty
      (K := K) := by
  intro state hclock T
  rcases hextract T with ⟨A⟩
  exact ⟨.associatedGradedCollision A⟩

end

end HC4.Valuation
