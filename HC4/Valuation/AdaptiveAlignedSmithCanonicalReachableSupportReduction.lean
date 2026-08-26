import HC4.Valuation.AdaptiveAlignedSmithCanonicalReachableJC2Resolution
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalSupportFrontier

/-!
# A19.8: collapse the reachable terminal to two source-support obligations

The current presented terminal has more historical rank-three constructors
than the final polynomial argument should see.  A18.5.21 already forgets that
history honestly: on the actual represented special fibre there are only two
finite-support outcomes.

* A concrete mixed-degree blocker exponent, carrying its full residual
  `MixedDegreeSmithExponentOutcome`.
* A nonempty canonical quadratic Smith refinement, every exponent of which is
  one of `(0,2,0)`, `(1,1,0)`, `(2,0,0)`.

A19.7 allows the two outcomes to terminate differently.  Accordingly this
file isolates the exact last two geometric producers:

* blocker support must produce one already-closed A18 polynomial obstruction;
* quadratic support must produce one honest associated-graded collision for
  the JC2 endpoint library.

Once those two producers are supplied on the reachable clock interval, the
mixed resolver and hence `JC2 => HC4` are automatic.  No terminal
cocharacter, balance relation or rank-line certificate is introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **The exact two remaining source-support producers.**

The fields consume the actual current terminal and the exact witnesses exposed
by A18.5.21.  In particular the quadratic producer is not allowed to receive a
Schur matrix in place of a polynomial endpoint. -/
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

  quadratic :
    ∀ {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
      (_hclock : state.rawDefect ≤ 6)
      (T : AdaptiveAlignedSmithCanonicalPresentedRankThreeTerminal
        canonicalAdaptiveAlignedSmithRepairRanking state 0)
      (_hne :
        (smithSymmetricBalancedSubface
          (smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
          0 (fun _ : SmithSupportExponent => (0 : ℤ))).Nonempty)
      (_hshape :
        ∀ e ∈ smithSymmetricBalancedSubface
          (smithProjectedSupport (1 : Fin 4) 2 3 T.specialFiber)
          0 (fun _ : SmithSupportExponent => (0 : ℤ)),
          (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
          (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
          (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)),
      Nonempty (TerminalAssociatedGradedCollisionData K)

/-- The A18.5.21 support split assembles the two local producers into the exact
mixed reachable-terminal resolver of A19.7. -/
noncomputable def
    AdaptiveAlignedSmithCanonicalReachableSupportProducer.toReachableResolution
    (P : AdaptiveAlignedSmithCanonicalReachableSupportProducer (K := K)) :
    AdaptiveAlignedSmithCanonicalReachableTerminalResolutionProperty
      (K := K) := by
  intro state hclock T
  rcases T.specialFiber_blocker_or_quadraticRefinement with hblock | hquad
  · rcases hblock with ⟨e, he, hpattern, houtcome⟩
    rcases P.blocker hclock T e he hpattern houtcome with ⟨O⟩
    exact ⟨.polynomialObstruction O⟩
  · rcases hquad with ⟨hne, hshape⟩
    rcases P.quadratic hclock T hne hshape with ⟨A⟩
    exact ⟨.associatedGradedCollision A⟩

/-- **Two-obligation `JC2 => HC4` reduction.**

After A18.5.21 there are no further terminal wrapper cases: proving the
blocker and quadratic producer fields above suffices for unrestricted HC4
under planar JC2. -/
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
