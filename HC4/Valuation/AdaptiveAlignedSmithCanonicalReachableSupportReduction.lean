import HC4.Valuation.AdaptiveAlignedSmithCanonicalReachableJC2Resolution
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalQuadraticPacket
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalQuadraticZeroClockEndpoint

/-!
# A19.14: the reachable support reduction after zero-clock quadratic closure

A19.10--13 sharpen the quadratic side of the current terminal classifier.
The complete surviving quadratic Smith face is an honest conformal initial
form.  When the source raw clock is zero, that *complete* face has Hessian
determinant one, retains the exact marked collision, and becomes the standard
one-zero endpoint after a coordinate permutation.  Thus no external producer
is required in the zero-clock quadratic branch.

The remaining source-level obligations are now strictly smaller:

* every concrete mixed-degree blocker exponent must produce one already-closed
  A18 polynomial obstruction;
* only a **positive-clock** quadratic terminal needs an additional honest
  associated-graded collision producer.

The positive branch still receives the A19.9 homogeneous collision packet,
including its actual source provenance.  No singular packet is promoted to a
Keller potential and no terminal cocharacter is manufactured.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **The two remaining source-level producers after A19.13.**

The quadratic producer is required only at positive raw determinant clock.
At clock zero A19.13 constructs the associated-graded one-zero endpoint
canonically from the complete quadratic Smith face. -/
structure AdaptiveAlignedSmithCanonicalReachableSupportProducer where
  blocker :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hclock : state.rawDefect ≤ 6)
      (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (e : SmithSupportExponent)
      (_he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
      (_hpattern :
        IsPureLongitudinalSmithPattern e ∨
        IsLowNegativeFirstSmithPattern e ∨
        IsLowNegativeSecondSmithPattern e ∨
        IsWLinearSmithPattern e)
      (_houtcome : MixedDegreeSmithExponentOutcome T.specialFiber e),
      Nonempty
        (AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction (K := K))

  quadraticPositive :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hclock : state.rawDefect ≤ 6)
      (_hpositive : 0 < state.rawDefect)
      (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_Q : AdaptiveAlignedSmithCanonicalTerminalQuadraticPacket T),
      Nonempty (TerminalAssociatedGradedCollisionData K)

/-- The lossless A19.10 support split assembles the remaining producers into
A19.7.  The zero-clock quadratic branch is discharged internally by A19.13;
only the positive-clock quadratic branch invokes `quadraticPositive`. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalReachableSupportProducer.toReachableResolution
    (P : AdaptiveAlignedSmithCanonicalReachableSupportProducer (K := K)) :
    AdaptiveAlignedSmithCanonicalReachableTerminalResolutionProperty
      (K := K) := by
  intro state hclock T
  rcases T.specialFiber_blocker_or_quadraticGeometry with hblock | G
  · rcases hblock with ⟨e, he, hpattern, houtcome⟩
    rcases P.blocker hclock T e he hpattern houtcome with ⟨O⟩
    exact ⟨.polynomialObstruction O⟩
  · by_cases hzero : state.rawDefect = 0
    · rcases G.quadraticFace_associatedGradedCollisionData_of_source_rawDefect_eq_zero
          hzero with ⟨A⟩
      exact ⟨.associatedGradedCollision A⟩
    · have hpositive : 0 < state.rawDefect := Nat.pos_of_ne_zero hzero
      rcases T.quadraticPacket_nonempty G.balancedNonempty G.quadratic with ⟨Q⟩
      rcases P.quadraticPositive hclock hpositive T Q with ⟨A⟩
      exact ⟨.associatedGradedCollision A⟩

/-- **Positive-clock support reduction for `JC2 => HC4`.**

After A19.13, unrestricted HC4 under planar JC2 requires no extra extraction
at zero-clock quadratic terminals.  The only quadratic extraction hypothesis
left is the positive-clock packet-to-associated-graded bridge, alongside the
concrete blocker-to-polynomial-obstruction producer. -/
theorem gradient_injective_of_hessianDeterminant_one_of_JC2_of_reachableSupportProducer
    (hJC2 : HC4.PlanarJC2Injectivity K)
    (P : AdaptiveAlignedSmithCanonicalReachableSupportProducer (K := K))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    Function.Injective (mvGradientMap F) := by
  exact
    gradient_injective_of_hessianDeterminant_one_of_JC2_of_reachableResolution
      hJC2 P.toReachableResolution F hdet

end

end HC4.Valuation
