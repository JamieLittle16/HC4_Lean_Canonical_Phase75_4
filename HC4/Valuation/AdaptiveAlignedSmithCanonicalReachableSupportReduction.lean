import HC4.Valuation.AdaptiveAlignedSmithCanonicalReachableJC2Resolution
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalQuadraticPacket
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalConformalZeroClockEndpoint

/-!
# A19.16: only strict-low blockers remain at zero clock

A19.15 strengthens the zero-clock conformal endpoint.  The complete degree-two
face for the source weight `(0,1,1,2)` is an honest one-zero JC2 endpoint as
soon as the three genuinely earlier Smith patterns

    (0,0,0), (0,1,0), (1,0,0)

are absent.  The `w`-linear pattern `(0,0,1)` has conformal degree two, is
retained exactly in the fourth gradient component, and no longer requires an
external blocker producer.

Consequently the remaining support producers split sharply by clock:

* at zero clock, only an actually supported strict-low pattern needs an
  unconditional A18 obstruction;
* at positive clock, a concrete four-pattern blocker still needs an A18
  obstruction;
* at positive clock, the surviving quadratic packet still needs the honest
  associated-graded JC2 bridge.

The zero-clock dispatcher searches for a strict-low exponent *before* invoking
the generic four-pattern support frontier, so a harmless `w`-linear witness can
never hide an earlier low blocker.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **The exact remaining source-level producers after A19.15.** -/
structure AdaptiveAlignedSmithCanonicalReachableSupportProducer where
  blockerZeroStrictLow :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hclock : state.rawDefect ≤ 6)
      (_hzero : state.rawDefect = 0)
      (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (e : SmithSupportExponent)
      (_he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
      (_hpattern :
        IsPureLongitudinalSmithPattern e ∨
        IsLowNegativeFirstSmithPattern e ∨
        IsLowNegativeSecondSmithPattern e)
      (_houtcome : MixedDegreeSmithExponentOutcome T.specialFiber e),
      Nonempty
        (AdaptiveAlignedSmithCanonicalTerminalPolynomialObstruction (K := K))

  blockerPositive :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hclock : state.rawDefect ≤ 6)
      (_hpositive : 0 < state.rawDefect)
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

/-- The reachable resolver first consumes zero clock using A19.15 unless an
actual strict-low exponent exists.  Positive clock then uses the old lossless
blocker/quadratic split. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalReachableSupportProducer.toReachableResolution
    (P : AdaptiveAlignedSmithCanonicalReachableSupportProducer (K := K)) :
    AdaptiveAlignedSmithCanonicalReachableTerminalResolutionProperty
      (K := K) := by
  intro state hclock T
  by_cases hzero : state.rawDefect = 0
  · by_cases hlow :
      ∃ e ∈ smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber,
        IsPureLongitudinalSmithPattern e ∨
        IsLowNegativeFirstSmithPattern e ∨
        IsLowNegativeSecondSmithPattern e
    · rcases hlow with ⟨e, he, hpattern⟩
      rcases T.specialFiber_axisData with ⟨hcoll, hgrad, hvalue⟩
      have houtcome : MixedDegreeSmithExponentOutcome T.specialFiber e :=
        projectedSmithExponent_mixedDegreeOutcome
          T.specialFiber e he hcoll hgrad hvalue
      rcases P.blockerZeroStrictLow hclock hzero T e he hpattern houtcome with ⟨O⟩
      exact ⟨.polynomialObstruction O⟩
    · have hno : T.HasNoStrictLowSmithPatterns := by
        intro e he
        constructor
        · intro hpure
          exact hlow ⟨e, he, Or.inl hpure⟩
        constructor
        · intro hfirst
          exact hlow ⟨e, he, Or.inr (Or.inl hfirst)⟩
        · intro hsecond
          exact hlow ⟨e, he, Or.inr (Or.inr hsecond)⟩
      rcases
          T.conformalDegreeTwoFace_associatedGradedCollisionData_of_source_rawDefect_eq_zero
            hzero hno with ⟨A⟩
      exact ⟨.associatedGradedCollision A⟩
  · have hpositive : 0 < state.rawDefect := Nat.pos_of_ne_zero hzero
    rcases T.specialFiber_blocker_or_quadraticGeometry with hblock | G
    · rcases hblock with ⟨e, he, hpattern, houtcome⟩
      rcases P.blockerPositive hclock hpositive T e he hpattern houtcome with ⟨O⟩
      exact ⟨.polynomialObstruction O⟩
    · rcases T.quadraticPacket_nonempty G.balancedNonempty G.quadratic with ⟨Q⟩
      rcases P.quadraticPositive hclock hpositive T Q with ⟨A⟩
      exact ⟨.associatedGradedCollision A⟩

/-- **Three-obligation support reduction for `JC2 => HC4`.**

Zero clock now needs an external producer only for the three strict-low Smith
patterns.  The `w`-linear and quadratic degree-two faces are consumed
internally by the canonical one-zero endpoint. -/
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
