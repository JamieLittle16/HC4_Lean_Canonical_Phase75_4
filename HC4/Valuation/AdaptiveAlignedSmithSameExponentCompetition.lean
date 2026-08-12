import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalFirstWall
import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalHomogeneousRigidity
import Mathlib.Tactic

/-!
# Same-exponent blocker competition

Longitudinal right recentering preserves the projected Smith support exactly.
Consequently the scalar first-wall candidate attached to a canonical blocker
can be chosen to be the *same projected Smith exponent* `e`.

This removes the anonymous candidate from the blocker-facing interface.  No
source scaling, no new family and no global progress claim are introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K]

/-- Same-exponent version of the recentered scalar first-wall competition. -/
def HasAlignedRecenteredSameExponentCompetition
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent)
    (base : SmithSupportExponent → ℤ) : Prop :=
  e ∈ smithProjectedSupport (1 : Fin 4) 2 3
      (longitudinalRightRecenterHom (K := K) F) ∧
    ((∃ emin ∈ smithProjectedSupport (1 : Fin 4) 2 3
          (longitudinalRightRecenterHom (K := K) F),
        (∀ q ∈ smithProjectedSupport (1 : Fin 4) 2 3
            (longitudinalRightRecenterHom (K := K) F),
          base emin ≤ base q) ∧
        base emin < base e) ∨
     (∃ emin ∈ smithProjectedSupport (1 : Fin 4) 2 3
          (longitudinalRightRecenterHom (K := K) F),
        (∀ q ∈ smithProjectedSupport (1 : Fin 4) 2 3
            (longitudinalRightRecenterHom (K := K) F),
          base emin ≤ base q) ∧
        base emin = base e ∧
        (IsOrdinaryDegreePureOnSmithLevel
            (longitudinalRightRecenterHom (K := K) F)
            base (base emin) ∨
         ∃ d₀ ∈ (longitudinalRightRecenterHom (K := K) F).support,
           ∃ d₁ ∈ (longitudinalRightRecenterHom (K := K) F).support,
             base (smithSupportExponentOf (1 : Fin 4) 2 3 d₀) =
               base emin ∧
             base (smithSupportExponentOf (1 : Fin 4) 2 3 d₁) =
               base emin ∧
             HC4.Polynomial.ordinaryDegree4 d₀ ≠
               HC4.Polynomial.ordinaryDegree4 d₁)))

/-- Every actual projected exponent of `F` enters the recentered scalar
competition as literally the same exponent. -/
theorem hasAlignedRecenteredSameExponentCompetition_of_mem
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent)
    (he : e ∈ smithProjectedSupport (1 : Fin 4) 2 3 F)
    (base : SmithSupportExponent → ℤ) :
    HasAlignedRecenteredSameExponentCompetition F e base := by
  let Frec := longitudinalRightRecenterHom (K := K) F
  let S := smithProjectedSupport (1 : Fin 4) 2 3 Frec

  have hcand : e ∈ S := by
    dsimp [S, Frec]
    exact recenteredProjectedSupport_mem_of_mem F e he

  refine ⟨by simpa [S, Frec] using hcand, ?_⟩

  rcases
      scalarMinimal_strictEarlier_or_tied S base e hcand with
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

/-- Forgetting that the candidate is literally `e` recovers the older
anonymous-candidate interface. -/
theorem HasAlignedRecenteredSameExponentCompetition.toFirstWallCompetition
    {F : MvPolynomial (Fin 4) K}
    {e : SmithSupportExponent}
    {base : SmithSupportExponent → ℤ}
    (h : HasAlignedRecenteredSameExponentCompetition F e base) :
    HasAlignedRecenteredFirstWallCompetition F e base := by
  rcases h with ⟨he, hcases⟩
  exact ⟨e, he, rfl, hcases⟩

/-- Every canonical aligned blocker admits the sharpened competition. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.sameExponentCompetition
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap)
    (base : SmithSupportExponent → ℤ) :
    HasAlignedRecenteredSameExponentCompetition
      B.aligned.endpoint.rawSpecialFiber B.exponent base := by
  exact
    hasAlignedRecenteredSameExponentCompetition_of_mem
      B.aligned.endpoint.rawSpecialFiber
      B.exponent B.mem base

/-- In particular the final explicit mixed-degree blocker retains the same
projected Smith exponent through recentering. -/
theorem AdaptiveAlignedSmithMixedDegreeBlockerEndpoint.sameExponentCompetition
    {degreeCap : ℕ}
    (M : AdaptiveAlignedSmithMixedDegreeBlockerEndpoint
      (K := K) degreeCap)
    (base : SmithSupportExponent → ℤ) :
    HasAlignedRecenteredSameExponentCompetition
      M.blocker.aligned.endpoint.rawSpecialFiber
      M.blocker.exponent base :=
  M.blocker.sameExponentCompetition base

/-- At the canonical zero scalar functional the strict-earlier alternative
is impossible, so only a tied degree-pure/mixed level remains. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.zeroBase_sameExponent_tied
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) :
    ∃ emin ∈ smithProjectedSupport (1 : Fin 4) 2 3
        (longitudinalRightRecenterHom
          (K := K) B.aligned.endpoint.rawSpecialFiber),
      (∀ q ∈ smithProjectedSupport (1 : Fin 4) 2 3
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber),
        (fun _ : SmithSupportExponent => (0 : ℤ)) emin ≤
          (fun _ : SmithSupportExponent => (0 : ℤ)) q) ∧
      (fun _ : SmithSupportExponent => (0 : ℤ)) emin =
        (fun _ : SmithSupportExponent => (0 : ℤ)) B.exponent ∧
      (IsOrdinaryDegreePureOnSmithLevel
          (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber)
          (fun _ : SmithSupportExponent => (0 : ℤ))
          ((fun _ : SmithSupportExponent => (0 : ℤ)) emin) ∨
       ∃ d₀ ∈ (longitudinalRightRecenterHom
            (K := K) B.aligned.endpoint.rawSpecialFiber).support,
         ∃ d₁ ∈ (longitudinalRightRecenterHom
              (K := K) B.aligned.endpoint.rawSpecialFiber).support,
           (fun _ : SmithSupportExponent => (0 : ℤ))
               (smithSupportExponentOf (1 : Fin 4) 2 3 d₀) =
             (fun _ : SmithSupportExponent => (0 : ℤ)) emin ∧
           (fun _ : SmithSupportExponent => (0 : ℤ))
               (smithSupportExponentOf (1 : Fin 4) 2 3 d₁) =
             (fun _ : SmithSupportExponent => (0 : ℤ)) emin ∧
           HC4.Polynomial.ordinaryDegree4 d₀ ≠
             HC4.Polynomial.ordinaryDegree4 d₁) := by
  have h :=
    B.sameExponentCompetition
      (fun _ : SmithSupportExponent => (0 : ℤ))
  rcases h with ⟨_he, hstrict | htied⟩
  · rcases hstrict with ⟨emin, hemin, hleast, hlt⟩
    simp at hlt
  · exact htied

end

end HC4.Valuation
