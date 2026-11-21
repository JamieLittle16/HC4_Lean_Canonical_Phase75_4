import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesUnramifiedFrontier
import HC4.Valuation.AdaptiveSectionBoundaryCollisionCovariance
import HC4.Valuation.AdaptiveSectionBoundaryShearFamily
import Mathlib.Tactic

/-!
# A19.31: same-scale geometric restart at an early positive Rees frontier

A19.30 removes the artificial factor-two parameter cover from every strict
early positive transverse Rees frontier.  This file packages that honest
ramification-one exposure back into the scale-aware state space.

The pulled right section need not already specialize to the marked axis: its
transverse constant terms record the section contact.  The canonical three
transverse determinant-one shears remove exactly those constants while fixing
the longitudinal marked coordinate.  Hessian defect, nonlinear degree cap,
and exact gradient collision are preserved by that shear.

Thus an early frontier of weight `r` gives a genuine state at the *same*
parameter scale and with the same repair tag, whose raw clock is `Delta-r`.
No recursion through a ramified presentation is asserted here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Ramification index one is the identity on polynomial sections. -/
private theorem parameterRamificationSection_one
    (a : Fin 4 → Polynomial K) :
    parameterRamificationSection (K := K) 1 a = a := by
  funext i
  simp [parameterRamificationSection, parameterRamificationHom_apply]

/-- The integral pullback of the zero section through any natural diagonal is
again literally zero. -/
private theorem integralAdaptiveSmithSection_zero
    (W : Fin 4 → ℕ)
    (hzero : HasIntegralAdaptiveSmithSection
      W (zeroPolynomialSection (K := K))) :
    integralAdaptiveSmithSection W
        (zeroPolynomialSection (K := K)) hzero =
      zeroPolynomialSection (K := K) := by
  funext i
  have hinflate := congrFun
    (adaptiveSmithInflateSection_integralSection_eq
      W (zeroPolynomialSection (K := K)) hzero) i
  have heq :
      Polynomial.X ^ W i *
          integralAdaptiveSmithSection W
            (zeroPolynomialSection (K := K)) hzero i =
        Polynomial.X ^ W i * 0 := by
    simpa [adaptiveSmithInflateSection, zeroPolynomialSection] using hinflate
  have hcancel := polynomial_X_pow_mul_cancel (K := K) (W i) heq
  simpa [zeroPolynomialSection] using hcancel

/-- **A19.31 same-scale unramified restart geometry.**

Whenever the maximal positive Rees section frontier stops strictly before the
incoming determinant clock, the represented family has a genuine successor
with the same scale and repair metadata and strictly smaller raw defect.
The construction uses only ramification index one and determinant-one source
shears. -/
theorem
    ScaleAwareAdaptiveGeometricRestartState.exists_positiveTransverseRees_unramifiedRestart
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hpositive : 0 < s.rawDefect)
    (hbound : HasCanonicalPositiveTransverseReesCoefficientBound
      s.rawDefect s.family)
    (hlt : canonicalPositiveTransverseSectionFrontierWeight
      s.rawDefect s.movingSection < s.rawDefect) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      target.rawDefect =
        s.rawDefect - canonicalPositiveTransverseSectionFrontierWeight
          s.rawDefect s.movingSection ∧
      target.scale = s.scale ∧
      target.degreeCap = s.degreeCap ∧
      target.sourceComplexity = s.sourceComplexity ∧
      target.repair = s.repair ∧
      target.rawDefect < s.rawDefect := by
  let r := canonicalPositiveTransverseSectionFrontierWeight
    s.rawDefect s.movingSection
  rcases exists_canonicalPositiveTransverseRees_unramifiedFrontier
      (K := K) s.rawDefect s.family s.hessianDefect hbound
      s.movingSection hlt with
    ⟨half, hrs, hint, hsection, hdef⟩
  let W := canonicalPositiveTransverseReesWeight half
  let hzero := canonicalPositiveTransverseRees_half_zero_hasIntegralSection
    (K := K) half
  let Pexp := adaptiveSmithExposureFamily 1 W r s.family hint
  let aexp := integralAdaptiveSmithSection W
    (zeroPolynomialSection (K := K)) hzero
  let bexp := integralAdaptiveSmithSection W s.movingSection hsection

  have haexp : aexp = zeroPolynomialSection (K := K) := by
    dsimp [aexp]
    exact integralAdaptiveSmithSection_zero W hzero

  have hcollRam :=
    polynomialFamilyExactGradientCollision_parameterRamification
      (K := K) 1 s.family
      (zeroPolynomialSection (K := K)) s.movingSection s.exactCollision
  have hcollRam' :
      HasPolynomialFamilyExactGradientCollision
        (parameterRamificationFamily (K := K) 1 s.family)
        (zeroPolynomialSection (K := K)) s.movingSection := by
    simpa [parameterRamificationSection_one] using hcollRam
  have hcollExp :
      HasPolynomialFamilyExactGradientCollision
        Pexp (zeroPolynomialSection (K := K)) bexp := by
    have h := polynomialFamilyExactGradientCollision_adaptiveSmithExposure
      1 W r (by norm_num) s.family hint
      (zeroPolynomialSection (K := K)) s.movingSection
      hzero hsection hcollRam'
    rw [haexp] at h
    simpa [Pexp, aexp, bexp] using h

  have hdegreeExp : NonlinearDegreeBound s.degreeCap Pexp := by
    dsimp [Pexp]
    exact nonlinearDegreeBound_adaptiveSmithExposureFamily
      s.degreeCap 1 r W s.family hint s.nonlinearDegreeBound

  have hbexp0 : polynomialSectionSpecialPoint bexp (0 : Fin 4) = 1 := by
    have hinflate := congrFun
      (adaptiveSmithInflateSection_integralSection_eq
        W s.movingSection hsection) (0 : Fin 4)
    have hW0 : W (0 : Fin 4) = 0 := by
      simp [W, canonicalPositiveTransverseReesWeight]
    have hb0 : bexp (0 : Fin 4) = s.movingSection (0 : Fin 4) := by
      simpa [adaptiveSmithInflateSection, hW0, bexp] using hinflate
    have hs0 := congrFun s.sectionSpecial (0 : Fin 4)
    change Polynomial.constantCoeff (bexp (0 : Fin 4)) = 1
    rw [hb0]
    simpa [polynomialSectionSpecialPoint, coordinateAxisPoint] using hs0

  let Pnext := pointedBoundaryShearFamily bexp Pexp
  let bnext := pointedBoundarySequentialUnshearSection bexp

  have hdefNext :
      HasPolynomialFamilyHessianDefect (K := K) Pnext
        (s.rawDefect - r) := by
    dsimp [Pnext]
    exact hessianDefect_pointedBoundaryShearFamily
      (s.rawDefect - r) bexp Pexp (by simpa [r, Pexp] using hdef)

  have hdegreeNext : NonlinearDegreeBound s.degreeCap Pnext := by
    dsimp [Pnext]
    exact nonlinearDegreeBound_pointedBoundaryShearFamily
      s.degreeCap bexp Pexp hdegreeExp

  have hcollNext :
      HasPolynomialFamilyExactGradientCollision
        Pnext (zeroPolynomialSection (K := K)) bnext := by
    dsimp [Pnext, bnext]
    exact polynomialFamilyExactGradientCollision_pointedBoundaryShear
      Pexp bexp hcollExp

  have hspecialNext :
      polynomialSectionSpecialPoint bnext =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    dsimp [bnext]
    exact pointedBoundarySequentialUnshearSection_special_eq_axis
      bexp hbexp0

  let target : ScaleAwareAdaptiveGeometricRestartState (K := K) := {
    rawDefect := s.rawDefect - r
    scale := s.scale
    scale_pos := s.scale_pos
    degreeCap := s.degreeCap
    sourceComplexity := s.sourceComplexity
    repair := s.repair
    family := Pnext
    movingSection := bnext
    hessianDefect := hdefNext
    nonlinearDegreeBound := hdegreeNext
    exactCollision := hcollNext
    sectionSpecial := hspecialNext
  }

  have hrpos : 0 < r :=
    s.canonicalPositiveTransverseSectionFrontierWeight_pos hpositive
  have hdrop : s.rawDefect - r < s.rawDefect := by
    omega
  refine ⟨target, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · rfl
  · rfl
  · rfl
  · rfl
  · exact hdrop

end

end HC4.Valuation