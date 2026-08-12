import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalFirstWall
import Mathlib.Tactic

/-!
# Canonical zero-base blocker competition

The global adaptive Smith entry already has a canonical geometrically
realizable scalar wall with constant base `0`.

Specialising the recentered blocker first-wall competition to this base
removes an artificial unresolved branch: a "strictly earlier scalar wall"
would require

    0 < 0,

hence is impossible.

Therefore every blocker on the canonical zero-base wall is reduced to:

* the already-existing general surviving Smith-grade shape; or
* a tied scalar wall that is ordinary-degree pure; or
* a tied scalar wall containing two explicit source monomials of unequal
  ordinary degree.

This file is only a logical specialization of already-green first-wall
machinery.  It does not yet route the tied degree-pure or mixed-degree
outputs into their downstream geometric consumers.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- The canonical scalar Smith functional used here. -/
def canonicalZeroSmithBase : SmithSupportExponent → ℤ :=
  fun _ => 0

/-- A zero-base first-wall competition cannot have a strictly earlier
competitor.  Hence only the two tied-wall outcomes remain. -/
theorem zeroBaseFirstWallCompetition_degreePure_or_mixedPair
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent)
    (h :
      HasAlignedRecenteredFirstWallCompetition
        F e canonicalZeroSmithBase) :
    IsOrdinaryDegreePureOnSmithLevel
        (longitudinalRightRecenterHom (K := K) F)
        canonicalZeroSmithBase 0 ∨
      ∃ d₀ ∈ (longitudinalRightRecenterHom (K := K) F).support,
        ∃ d₁ ∈ (longitudinalRightRecenterHom (K := K) F).support,
          HC4.Polynomial.ordinaryDegree4 d₀ ≠
            HC4.Polynomial.ordinaryDegree4 d₁ := by
  rcases h with
    ⟨ecand, hecand, hgrade, hstrict | htied⟩

  · rcases hstrict with
      ⟨emin, hemin, hleast, hlt⟩
    dsimp [canonicalZeroSmithBase] at hlt
    omega

  · rcases htied with
      ⟨emin, hemin, hleast, heq, hpure | hmixed⟩

    · left
      simpa [canonicalZeroSmithBase] using hpure

    · right
      rcases hmixed with
        ⟨d₀, hd₀, d₁, hd₁, hlevel₀, hlevel₁, hdegree⟩
      exact ⟨d₀, hd₀, d₁, hd₁, hdegree⟩

/-- Strong canonical specialization.  Because every canonical blocker
enters the recentered first-wall competition directly, the zero-base wall
has only the honest tied alternatives: degree-pure or an explicit
mixed-degree pair. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.zeroBaseDegreePure_or_mixedPair
    [CharZero K]
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) :
    IsOrdinaryDegreePureOnSmithLevel
        (longitudinalRightRecenterHom
          (K := K) B.aligned.endpoint.rawSpecialFiber)
        canonicalZeroSmithBase 0 ∨
      ∃ d₀ ∈
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber).support,
        ∃ d₁ ∈
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber).support,
          HC4.Polynomial.ordinaryDegree4 d₀ ≠
            HC4.Polynomial.ordinaryDegree4 d₁ := by
  exact
    zeroBaseFirstWallCompetition_degreePure_or_mixedPair
      B.aligned.endpoint.rawSpecialFiber B.exponent
      (B.firstWallCompetition canonicalZeroSmithBase)

/-- Dispatcher-facing specialization.

On the canonical zero scalar wall, every aligned blocker is already in the
surviving Smith-grade shape, or lies on a tied degree-pure wall, or exhibits
an explicit mixed-degree pair.

The arbitrary scalar-base realizability obligation is therefore absent from
this canonical path.
-/
theorem AdaptiveAlignedSmithBlockerEndpoint.survivingShape_or_zeroBaseDegreePure_or_mixedPair
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) :
    HasGeneralSurvivingSmithGradeShape B.exponent ∨
      IsOrdinaryDegreePureOnSmithLevel
        (longitudinalRightRecenterHom
          (K := K) B.aligned.endpoint.rawSpecialFiber)
        canonicalZeroSmithBase 0 ∨
      ∃ d₀ ∈
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber).support,
        ∃ d₁ ∈
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber).support,
          HC4.Polynomial.ordinaryDegree4 d₀ ≠
            HC4.Polynomial.ordinaryDegree4 d₁ := by
  rcases
      B.survivingShape_or_firstWallCompetition
        canonicalZeroSmithBase with
    hshape | hwall
  · exact Or.inl hshape
  · right
    exact
      zeroBaseFirstWallCompetition_degreePure_or_mixedPair
        B.aligned.endpoint.rawSpecialFiber B.exponent hwall

end

end HC4.Valuation
