import HC4.Valuation.AdaptiveAlignedSmithCanonicalHC4ZeroStrictLowSingularReduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction
import HC4.Newton.TerminalAssociatedGradedEndpoint

/-!
# Final source-honest resolution interface for the zero-strict-low singular seam

The sound unrestricted HC4 front door reduces determinant-one gradient
injectivity to impossibility of
`AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData`.

At this boundary, neither a finite repair promotion nor abstract rank geometry
is itself contradictory.  The final local producer must return an honest
polynomial-level object that an existing endpoint theorem can consume.

This file fixes that interface once and for all.  A singular terminal is
resolved only by one of:

* an already-verified unconditional terminal polynomial obstruction; or
* an honest associated-graded polynomial collision carrying a certified
  terminal endpoint, contradictory under planar JC2.

No repair-only constructor, global-progress-only constructor, or Schur-clock
constructor appears here.  The difficult geometric producer is deliberately
left to subsequent files.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- Sound final objects that may resolve one concrete zero-strict-low singular
terminal.

The terminal is retained as an index so later producer theorems are forced to
work at the actually reached source.  The constructors themselves contain only
objects with already-verified polynomial endpoint consumers. -/
inductive AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) : Type (u + 1)
  | polynomialObstruction
      (O : AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction (K := K))
  | associatedGradedCollision
      (A : TerminalAssociatedGradedCollisionData K)

/-- The geometric producer property required from the remaining local seam. -/
def AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolutionProperty :
    Prop :=
  ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)},
    ∀ T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state,
      Nonempty
        (AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution

/-- Every permitted final-resolution object is contradictory under planar JC2.

The polynomial-obstruction branch is unconditional; JC2 is used only by the
honest associated-graded collision branch. -/
theorem impossible_of_JC2
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state}
    (R : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution T)
    (hJC2 : HC4.PlanarJC2Injectivity K) :
    False := by
  cases R with
  | polynomialObstruction O =>
      exact O.impossible
  | associatedGradedCollision A =>
      exact A.impossible_of_JC2 hJC2

end AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolution

/-- A completed final-resolution producer makes every sound singular terminal
impossible under planar JC2. -/
theorem
    AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData.impossible_of_JC2_of_finalResolution
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (hresolve :
      AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolutionProperty
        (K := K))
    {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
      (K := K) state) :
    False := by
  rcases hresolve T with ⟨R⟩
  exact R.impossible_of_JC2 hJC2

/-- **Conditional final assembly through the sound singular carrier.**

Once the remaining geometry produces the final-resolution interface at every
zero-strict-low singular terminal, planar JC2 implies injectivity of every
four-variable polynomial gradient with Hessian determinant one. -/
theorem
    gradient_injective_of_hessianDeterminant_one_of_JC2_of_zeroStrictLowSingularFinalResolution
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (hresolve :
      AdaptiveAlignedSmithCanonicalZeroStrictLowSingularFinalResolutionProperty
        (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) := by
  exact
    gradient_injective_of_hessianDeterminant_one_of_zeroStrictLowSingularTerminal_impossible
      (fun T => T.impossible_of_JC2_of_finalResolution hJC2 hresolve)
      F hdet

end

end HC4.Valuation
