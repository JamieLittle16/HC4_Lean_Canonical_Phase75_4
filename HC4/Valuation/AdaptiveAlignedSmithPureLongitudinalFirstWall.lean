import HC4.Valuation.AdaptiveAlignedSmithBlockerFirstWall
import Mathlib.Tactic

/-!
# Pure-longitudinal blocker closure by projected-support invariance

The previous blocker adapter reduced the concrete blocker branch to one
apparent exception: a pure-longitudinal residual whose factorization occurs
in the derivative of the axis restriction.

For the dispatcher-facing first-wall interface, no separate Taylor lifting is
actually necessary.

The current mixed-degree Newton library proves the stronger geometric fact

    smithProjectedSupport (recenter F) = smithProjectedSupport F.

Longitudinal right recentering may change the actual longitudinal exponent of
a monomial, but after forgetting that exponent it preserves the projected
Smith support exactly.  Hence every blocker exponent already supplies a
recentered projected-support candidate with the same Smith grade.

A finite scalar minimum then gives the same exhaustive first-wall
competition used by the transverse residual theorem.

This closes the pure-longitudinal exception without manufacturing a new
family and without imposing any artificial order on the pair-valued Smith
grade.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K]

/-- Any projected Smith exponent survives longitudinal right recentering as a
projected exponent.  Only its hidden longitudinal source exponent may change. -/
theorem recenteredProjectedSupport_mem_of_mem
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F) :
    e ∈ smithProjectedSupport (1 : Fin 4) 2 3
      (longitudinalRightRecenterHom (K := K) F) := by
  rw [smithProjectedSupport_longitudinalRightRecenterHom]
  exact he

/-- **Generic projected-support first-wall competition after recentering.**

Every actual projected exponent of `F` may itself be used as the candidate
after longitudinal right recentering.  Comparing it with a genuine scalar
minimum yields either a strictly earlier wall or a tied wall; a tied wall is
then split into ordinary-degree-pure and genuinely mixed-degree cases by the
existing finite competition theorem. -/
theorem hasAlignedRecenteredFirstWallCompetition_of_mem
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F)
    (base : SmithSupportExponent → ℤ) :
    HasAlignedRecenteredFirstWallCompetition F e base := by
  let Frec :=
    longitudinalRightRecenterHom (K := K) F
  let S :=
    smithProjectedSupport (1 : Fin 4) 2 3 Frec

  have hcand : e ∈ S := by
    dsimp [S, Frec]
    exact recenteredProjectedSupport_mem_of_mem F e he

  refine ⟨e, ?_, rfl, ?_⟩
  · simpa [S, Frec] using hcand

  rcases
      scalarMinimal_strictEarlier_or_tied
        S base e hcand with
    ⟨emin, hemin, hleast, hstrict | htied⟩

  · left
    exact
      ⟨emin,
        by simpa [S, Frec] using hemin,
        by
          intro q hq
          apply hleast q
          simpa [S, Frec] using hq,
        hstrict⟩

  · right
    have hlevel :
        ∃ q ∈ smithProjectedSupport (1 : Fin 4) 2 3 Frec,
          base q = base emin := by
      exact
        ⟨emin,
          by simpa [S, Frec] using hemin,
          rfl⟩

    rcases
        scalarSmithLevel_degreePure_or_mixedPair
          Frec base (base emin) hlevel with
      hpure | hmixed

    · exact
        ⟨emin,
          by simpa [S, Frec] using hemin,
          by
            intro q hq
            apply hleast q
            simpa [S, Frec] using hq,
          htied,
          Or.inl hpure⟩

    · exact
        ⟨emin,
          by simpa [S, Frec] using hemin,
          by
            intro q hq
            apply hleast q
            simpa [S, Frec] using hq,
          htied,
          Or.inr hmixed⟩

/-- The previously exceptional pure-longitudinal blocker enters exactly the
same recentered first-wall competition as the transverse blockers.

The residual normal form is retained in `P`, but no additional property of it
is required at this interface because projected-support invariance is
stronger than the individual Taylor support witness needed earlier. -/
theorem AdaptiveAlignedSmithPureLongitudinalResidual.firstWallCompetition
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap}
    (P : AdaptiveAlignedSmithPureLongitudinalResidual
      (K := K) B)
    (base : SmithSupportExponent → ℤ) :
    HasAlignedRecenteredFirstWallCompetition
      B.aligned.endpoint.rawSpecialFiber B.exponent base := by
  exact
    hasAlignedRecenteredFirstWallCompetition_of_mem
      B.aligned.endpoint.rawSpecialFiber
      B.exponent B.mem base

/-- **Concrete blocker closure.**

Every fully normalized concrete blocker now enters the same genuine
recentered scalar first-wall competition.  The distinction between
pure-longitudinal and transverse residuals disappears at the dispatcher
boundary. -/
theorem AdaptiveAlignedSmithConcreteBlockerResidualNormalForm.firstWallCompetition
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap}
    (R :
      AdaptiveAlignedSmithConcreteBlockerResidualNormalForm
        (K := K) B)
    (base : SmithSupportExponent → ℤ) :
    HasAlignedRecenteredFirstWallCompetition
      B.aligned.endpoint.rawSpecialFiber B.exponent base := by
  rcases R.pureLongitudinal_or_firstWallCompetition base with
    hpure | hwall
  · rcases hpure with ⟨P⟩
    exact P.firstWallCompetition base
  · exact hwall


/-- Strong canonical first-wall handoff.  The blocker pattern itself
reconstructs a concrete residual, so there is no genuine surviving-shape
escape before entering the recentered scalar competition. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.firstWallCompetition
    [CharZero K]
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap)
    (base : SmithSupportExponent → ℤ) :
    HasAlignedRecenteredFirstWallCompetition
      B.aligned.endpoint.rawSpecialFiber B.exponent base := by
  rcases B.concreteResidualNormalForm with ⟨R⟩
  exact R.firstWallCompetition base

/-- **Aligned blocker dispatcher closure at the first-wall interface.**

The blocker endpoint has only two honest outputs left:

* the already-existing general surviving Smith-grade shape; or
* an actual recentered scalar first-wall competition.

Thus there is no longer a special pure-longitudinal blocker branch. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.survivingShape_or_firstWallCompetition
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap)
    (base : SmithSupportExponent → ℤ) :
    HasGeneralSurvivingSmithGradeShape B.exponent ∨
      HasAlignedRecenteredFirstWallCompetition
        B.aligned.endpoint.rawSpecialFiber B.exponent base := by
  rcases B.concreteResidualNormalForm_or_survivingShape with
    hconcrete | hsurviving
  · right
    rcases hconcrete with ⟨R⟩
    exact R.firstWallCompetition base
  · exact Or.inl hsurviving


end

end HC4.Valuation
