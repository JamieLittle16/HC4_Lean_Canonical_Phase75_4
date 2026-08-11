import HC4.Valuation.AdaptiveAlignedSmithBlockerResidual
import HC4.Newton.MixedDegreeFirstWallCompetition
import Mathlib.Tactic

/-!
# Aligned blocker residuals enter the recentered first-wall competition

The mixed-degree Newton library already contains the genuine geometric
interpretation of every terminal *transverse* blocker residual.

If

    longitudinalCoefficientPolynomial e.b e.c e.d F
      = X * (X - 1) * B

and `B` has been completely normalized by `EndpointResidualNormalForm`, then
`recenteredTerminalResidual_firstWallCompetition` constructs an actual
projected-support candidate of the right-recentered polynomial, with the
original Smith grade, and compares it against a true minimum of any supplied
scalar wall functional.

This file attaches that theorem to the three transverse constructors of the
new aligned blocker endpoint:

* low-negative-first;
* low-negative-second;
* w-linear.

The pure-longitudinal blocker is retained explicitly.  Its residual lives in
the derivative of the axis restriction rather than in a transverse
coefficient polynomial, so applying the transverse theorem to it would be a
type-level sleight of hand.  It is now the only concrete blocker case left
for a bespoke recentered support lemma.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u

variable {K : Type u} [Field K]

/-! ## A reusable name for the existing first-wall output -/

/-- The exact scalar first-wall competition produced by one recentered
terminal residual candidate.

The pair-valued Smith grade is retained, but first-wall order is controlled
by the supplied scalar functional `base`. -/
def HasAlignedRecenteredFirstWallCompetition
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent)
    (base : SmithSupportExponent → ℤ) : Prop :=
  ∃ ecand ∈ smithProjectedSupport (1 : Fin 4) 2 3
      (longitudinalRightRecenterHom (K := K) F),
    ecand.grade = e.grade ∧
    ((∃ emin ∈ smithProjectedSupport (1 : Fin 4) 2 3
          (longitudinalRightRecenterHom (K := K) F),
        (∀ q ∈ smithProjectedSupport (1 : Fin 4) 2 3
            (longitudinalRightRecenterHom (K := K) F),
          base emin ≤ base q) ∧
        base emin < base ecand) ∨
     (∃ emin ∈ smithProjectedSupport (1 : Fin 4) 2 3
          (longitudinalRightRecenterHom (K := K) F),
        (∀ q ∈ smithProjectedSupport (1 : Fin 4) 2 3
            (longitudinalRightRecenterHom (K := K) F),
          base emin ≤ base q) ∧
        base emin = base ecand ∧
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

/-- The existing Newton theorem, repackaged under the dispatcher-facing
predicate above. -/
theorem hasAlignedRecenteredFirstWallCompetition_of_terminalResidual
    (F : MvPolynomial (Fin 4) K)
    (e : SmithSupportExponent)
    (R : Polynomial K)
    (hfactor :
      longitudinalCoefficientPolynomial e.b e.c e.d F =
        (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * R)
    (hnormal : EndpointResidualNormalForm R)
    (base : SmithSupportExponent → ℤ) :
    HasAlignedRecenteredFirstWallCompetition F e base := by
  exact
    recenteredTerminalResidual_firstWallCompetition
      F e R hfactor hnormal base

/-! ## The one concrete blocker not covered by the transverse API -/

/-- The retained pure-longitudinal terminal residual.  This is the only
concrete blocker whose normalized residual occurs in the derivative of the
axis restriction instead of a transverse longitudinal coefficient. -/
structure AdaptiveAlignedSmithPureLongitudinalResidual
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap) where
  axis : Polynomial K
  residual : Polynomial K
  pattern : IsPureLongitudinalSmithPattern B.exponent
  axis_ne_zero : axis ≠ 0
  axis_eq :
    axis =
      longitudinalAxisRestriction
        B.aligned.endpoint.rawSpecialFiber
  residual_ne_zero : residual ≠ 0
  derivative_factor :
    axis.derivative =
      (Polynomial.X * (Polynomial.X - Polynomial.C 1)) * residual
  degree_drop :
    residual.natDegree < axis.derivative.natDegree
  normal : EndpointResidualNormalForm residual

/-! ## Three transverse constructors are already geometrically closed -/

/-- Any concrete blocker normal form is now either the sole pure-longitudinal
case, or it already enters the genuine recentered scalar first-wall
competition.

This theorem is intentionally parameterized by `base`: the existing Newton
machinery correctly distinguishes the pair-valued Smith grade from the
scalar functional that orders first walls. -/
theorem AdaptiveAlignedSmithConcreteBlockerResidualNormalForm.pureLongitudinal_or_firstWallCompetition
    {degreeCap : ℕ}
    {B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap}
    (R :
      AdaptiveAlignedSmithConcreteBlockerResidualNormalForm
        (K := K) B)
    (base : SmithSupportExponent → ℤ) :
    Nonempty
        (AdaptiveAlignedSmithPureLongitudinalResidual
          (K := K) B) ∨
      HasAlignedRecenteredFirstWallCompetition
        B.aligned.endpoint.rawSpecialFiber B.exponent base := by
  cases R with
  | pureLongitudinal A C hpattern hA hAeq hC hfactor hdegree normal =>
      exact Or.inl
        ⟨{
          axis := A
          residual := C
          pattern := hpattern
          axis_ne_zero := hA
          axis_eq := hAeq
          residual_ne_zero := hC
          derivative_factor := hfactor
          degree_drop := hdegree
          normal := normal
        }⟩

  | lowNegativeFirst A C hpattern hA hAeq hC hfactor hdegree normal =>
      right
      apply hasAlignedRecenteredFirstWallCompetition_of_terminalResidual
        B.aligned.endpoint.rawSpecialFiber B.exponent C
      · exact hAeq.symm.trans hfactor
      · exact normal

  | lowNegativeSecond A C hpattern hA hAeq hC hfactor hdegree normal =>
      right
      apply hasAlignedRecenteredFirstWallCompetition_of_terminalResidual
        B.aligned.endpoint.rawSpecialFiber B.exponent C
      · exact hAeq.symm.trans hfactor
      · exact normal

  | wLinear A C hpattern hA hAeq hC hfactor hdegree normal =>
      right
      apply hasAlignedRecenteredFirstWallCompetition_of_terminalResidual
        B.aligned.endpoint.rawSpecialFiber B.exponent C
      · exact hAeq.symm.trans hfactor
      · exact normal


/-! ## Dispatcher-facing blocker reduction -/

/-- The aligned canonical blocker is reduced to exactly three possibilities:

1. a general surviving Smith-grade shape already belonging to the surviving
   geometry;
2. the single pure-longitudinal residual case;
3. an actual recentered first-wall competition.

Thus all transverse blocker residual recursion is completely absorbed by
existing Newton machinery. -/
theorem AdaptiveAlignedSmithBlockerEndpoint.survivingShape_or_pureLongitudinal_or_firstWallCompetition
    {degreeCap : ℕ}
    (B : AdaptiveAlignedSmithBlockerEndpoint
      (K := K) degreeCap)
    (base : SmithSupportExponent → ℤ) :
    HasGeneralSurvivingSmithGradeShape B.exponent ∨
      Nonempty
        (AdaptiveAlignedSmithPureLongitudinalResidual
          (K := K) B) ∨
      HasAlignedRecenteredFirstWallCompetition
        B.aligned.endpoint.rawSpecialFiber B.exponent base := by
  rcases B.concreteResidualNormalForm_or_survivingShape with
    hconcrete | hsurviving
  · rcases hconcrete with ⟨R⟩
    rcases R.pureLongitudinal_or_firstWallCompetition base with
      hpure | hwall
    · exact Or.inr (Or.inl hpure)
    · exact Or.inr (Or.inr hwall)
  · exact Or.inl hsurviving


end

end HC4.Valuation
