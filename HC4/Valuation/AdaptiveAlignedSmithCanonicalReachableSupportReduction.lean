import HC4.Valuation.AdaptiveAlignedSmithCanonicalReachableJC2Resolution
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalSupportFrontier
import HC4.Valuation.AdaptiveAlignedSmithCanonicalTerminalQuadraticPacket

/-!
# A19.8: collapse the reachable terminal to two source-support obligations

The current presented terminal has more historical rank-three constructors
than the final polynomial argument should see.  A18.5.21 already forgets that
history honestly: on the actual represented special fibre there are only two
finite-support outcomes.

* A concrete mixed-degree blocker exponent, carrying its full residual
  `MixedDegreeSmithExponentOutcome`.
* A nonempty canonical quadratic Smith refinement.

A19.9 now consumes the whole finite-support construction in the second branch:
the quadratic refinement canonically yields an actual ordinary-homogeneous
packet with exact collision, zero Hessian determinant and persistent rank-one
support.  Thus the last two geometric producers can be stated at the strongest
honest interfaces already available:

* blocker support -> one already-closed A18 polynomial obstruction;
* homogeneous quadratic collision packet -> one honest associated-graded JC2
  endpoint.

Once those two producers are supplied on the reachable clock interval, the
mixed resolver and hence `JC2 => HC4` are automatic.  No terminal
cocharacter, balance relation or rank-line certificate is introduced here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- **The exact two remaining source-level producers.**

The blocker field consumes the actual mixed-degree residual witness.  The
quadratic field receives the honest homogeneous polynomial packet extracted by
A19.9, so it is not allowed to reinterpret a Schur matrix or a bare support
pattern as an associated-graded endpoint. -/
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
      (_Q : AdaptiveAlignedSmithCanonicalTerminalQuadraticPacket T),
      Nonempty (TerminalAssociatedGradedCollisionData K)

/-- The A18.5.21 support split, followed by the A19.9 packet extractor in the
quadratic branch, assembles the two local producers into the exact mixed
reachable-terminal resolver of A19.7. -/
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
    rcases T.quadraticPacket_nonempty hne hshape with ⟨Q⟩
    rcases P.quadratic hclock T Q with ⟨A⟩
    exact ⟨.associatedGradedCollision A⟩

/-- **Two-obligation `JC2 => HC4` reduction.**

After A18.5.21/A19.9 there are no further terminal wrapper or finite-support
construction cases: proving the blocker producer and the homogeneous-packet
JC2 producer above suffices for unrestricted HC4 under planar JC2. -/
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
