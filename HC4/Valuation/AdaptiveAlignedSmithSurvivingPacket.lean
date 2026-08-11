import HC4.Valuation.AdaptiveAlignedSmithSurvivingExposure
import HC4.Newton.MixedDegreeWallRefinement
import Mathlib.Tactic

/-!
# Surviving aligned-Smith wall to the existing persistent packet machinery

The assembled aligned-Smith dispatcher already lands in an
`IntegralAdaptiveSurvivingSmithWall` on the normalized special fibre of a
legacy-compatible adaptive state.

The current Newton machinery can consume precisely that object.

First, the same wall is refined by
`minimalSmithLevel_blockerOutcome_or_symmetricQuadraticRefinement`.  This
either discovers a residual blocker that must be returned to the blocker
continuation, or proves that the wall's *own* balanced Smith subface is
nonempty and consists only of the three binary quadratic patterns.

Second, the existing mixed-degree wall-refinement theorem extracts from that
same quadratic subface a minimal longitudinal homogeneous packet carrying:

* degree at least two;
* exact axis collision `0 ~ e0`;
* zero four-dimensional Hessian determinant;
* persistent rank-one packet support.

No new packet classification is proved here.  This file is only the missing
dispatcher adapter.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## The exact balanced subface of a surviving aligned wall -/

/-- The balanced Smith subface belonging to the exact wall retained by a
surviving aligned-Smith endpoint. -/
def AdaptiveAlignedSmithSurvivingStateEndpoint.balancedSubface
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s) :
    Finset SmithSupportExponent :=
  let a := W.original.aligned.toAdaptiveState s
  smithSymmetricBalancedSubface
    (smithProjectedSupport
      (1 : Fin 4) 2 3 a.normalizedSpecialFiber)
    W.wall.level W.wall.base

/-- A blocker discovered when the surviving wall is refined to the true
quadratic balanced face. -/
structure AdaptiveAlignedSmithRefinedBlockerEndpoint
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s) where
  exponent : SmithSupportExponent
  mem :
    exponent ∈
      smithProjectedSupport
        (1 : Fin 4) 2 3
        (W.original.aligned.toAdaptiveState s).normalizedSpecialFiber
  level :
    W.wall.base exponent = W.wall.level
  pattern :
    IsPureLongitudinalSmithPattern exponent ∨
    IsLowNegativeFirstSmithPattern exponent ∨
    IsLowNegativeSecondSmithPattern exponent ∨
    IsWLinearSmithPattern exponent
  outcome :
    MixedDegreeSmithExponentOutcome
      (W.original.aligned.toAdaptiveState s).normalizedSpecialFiber
      exponent

/-- The packet endpoint extracted from the exact balanced subface of the
surviving wall. -/
structure AdaptiveAlignedSmithPersistentPacketEndpoint
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s) where
  degree : ℕ
  packet : MvPolynomial (Fin 4) K
  quadratic :
    ∀ e ∈ W.balancedSubface s,
      (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
      (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
      (e.b = 2 ∧ e.c = 0 ∧ e.d = 0)
  provenance :
    IsMinimalLongitudinalSmithPacket
      (W.balancedSubface s)
      (W.original.aligned.toAdaptiveState s).normalizedSpecialFiber
      degree packet
  degree_ge_two : 2 ≤ degree
  exactCollision :
    HasExactGradientCollision packet
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4))
  hessian_zero :
    HC4.Polynomial.hessianDeterminant packet = 0
  persistent :
    HasRankOnePersistentPacketSupport
      (0 : Fin 4) 1 2 degree packet

/-- The balanced subface is, tautologically, a subface of the projected
support of the same retained wall. -/
theorem AdaptiveAlignedSmithSurvivingStateEndpoint.balancedSubface_subset
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s) :
    W.balancedSubface s ⊆
      smithProjectedSupport
        (1 : Fin 4) 2 3
        (W.original.aligned.toAdaptiveState s).normalizedSpecialFiber := by
  intro e he
  exact
    (mem_smithSymmetricBalancedSubface.mp
      (by simpa [AdaptiveAlignedSmithSurvivingStateEndpoint.balancedSubface]
        using he)).1

/-! ## Reuse of the existing mixed-degree refinement -/

/-- **Surviving wall -> refined blocker or persistent homogeneous packet.**

This is the static packet-level continuation of the surviving branch.  It
works even before deciding whether the retained determinant defect is zero
or positive; the positive-defect family-level exposure is supplied
separately by `zeroDefect_or_exposure`.
-/
theorem AdaptiveAlignedSmithSurvivingStateEndpoint.refinedBlocker_or_packet
    [CharZero K]
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (W : AdaptiveAlignedSmithSurvivingStateEndpoint (K := K) s) :
    Nonempty
        (AdaptiveAlignedSmithRefinedBlockerEndpoint
          (K := K) s W) ∨
      Nonempty
        (AdaptiveAlignedSmithPersistentPacketEndpoint
          (K := K) s W) := by
  let a := W.original.aligned.toAdaptiveState s

  have haxis :
      HasNormalizedSmithAxisData a.normalizedSpecialFiber := by
    simpa [a] using
      W.original.aligned.rawSpecialFiber_axisData

  rcases haxis with ⟨hcoll, hzero, hvalue⟩

  rcases
      minimalSmithLevel_blockerOutcome_or_symmetricQuadraticRefinement
        a.normalizedSpecialFiber
        W.wall.base
        W.wall.level
        hcoll
        hzero
        hvalue
        W.wall.symmetricMinimal
        W.wall.minimal
        W.wall.attained with
    hblock | hquad

  · left
    rcases hblock with
      ⟨e, he, hlevel, hpattern, houtcome⟩
    exact
      ⟨{
        exponent := e
        mem := by simpa [a] using he
        level := hlevel
        pattern := hpattern
        outcome := by simpa [a] using houtcome
      }⟩

  · right
    rcases hquad with ⟨hne, hquadratic⟩

    let T : Finset SmithSupportExponent :=
      smithSymmetricBalancedSubface
        (smithProjectedSupport
          (1 : Fin 4) 2 3 a.normalizedSpecialFiber)
        W.wall.level W.wall.base

    have hTnonempty : T.Nonempty := by
      simpa [T] using hne

    have hTsubset :
        T ⊆
          smithProjectedSupport
            (1 : Fin 4) 2 3 a.normalizedSpecialFiber := by
      intro e he
      exact (mem_smithSymmetricBalancedSubface.mp he).1

    have hTquad :
        ∀ e ∈ T,
          (e.b = 0 ∧ e.c = 2 ∧ e.d = 0) ∨
          (e.b = 1 ∧ e.c = 1 ∧ e.d = 0) ∨
          (e.b = 2 ∧ e.c = 0 ∧ e.d = 0) := by
      intro e he
      exact hquadratic e (by simpa [T] using he)

    rcases
        nonemptyQuadraticProjectedSubface_exists_minimalLongitudinalPacket
          T
          a.normalizedSpecialFiber
          hTnonempty
          hTsubset
          hTquad with
      ⟨D, Q, hprov, hD, hQcoll, hQhess, hpersistent⟩

    exact
      ⟨{
        degree := D
        packet := Q
        quadratic := by
          intro e he
          exact hTquad e
            (by
              simpa [T,
                AdaptiveAlignedSmithSurvivingStateEndpoint.balancedSubface,
                a] using he)
        provenance := by
          simpa [T,
            AdaptiveAlignedSmithSurvivingStateEndpoint.balancedSubface,
            a] using hprov
        degree_ge_two := hD
        exactCollision := hQcoll
        hessian_zero := hQhess
        persistent := hpersistent
      }⟩

end

end HC4.Valuation
