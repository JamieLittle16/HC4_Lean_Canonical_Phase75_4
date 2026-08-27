import HC4.Valuation.AdaptiveAlignedSmithCanonicalPositiveTransverseReesUnramifiedFrontier
import HC4.Valuation.AdaptiveSectionBoundaryReentry
import Mathlib.Tactic

/-!
# A19.31: package an early unramified Rees frontier as an honest same-scale state

A19.30 removes the artificial factor-two parameter cover from every strict
early positive transverse Rees frontier.  This file performs the remaining
geometric bookkeeping on that ramification-one exposure.

The integral left section is still zero.  The integral right section retains
longitudinal special value `1`; its transverse special coordinates may be
arbitrary.  The already-green determinant-one three-shear normalises that
right special point back to the marked axis point `e₀`, preserving exact
collision, nonlinear source degree, and the Hessian clock.

Thus every strict early frontier gives a genuine scale-aware state at the same
literal scale and repair tag, with raw clock `Delta - r < Delta`.

No recursion or new progress relation is introduced here.  Final assembly must
consume this earlier same-scale exposure through the existing A18 first-contact
architecture.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

@[simp] theorem parameterRamificationHom_one_apply
    (p : Polynomial K) :
    parameterRamificationHom (K := K) 1 p = p := by
  rw [parameterRamificationHom_apply]
  simp

@[simp] theorem parameterRamificationFamily_one
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    parameterRamificationFamily (K := K) 1 P = P := by
  apply MvPolynomial.ext
  intro d
  simp [parameterRamificationFamily]

@[simp] theorem parameterRamificationSection_one
    (b : Fin 4 → Polynomial K) :
    parameterRamificationSection (K := K) 1 b = b := by
  funext i
  simp [parameterRamificationSection]

/-- Pulling the zero section through an integral diagonal leaves it zero. -/
theorem integralAdaptiveSmithSection_zero_eq
    (W : Fin 4 → ℕ)
    (hdiv : HasIntegralAdaptiveSmithSection
      W (zeroPolynomialSection (K := K))) :
    integralAdaptiveSmithSection W
        (zeroPolynomialSection (K := K)) hdiv =
      zeroPolynomialSection (K := K) := by
  funext i
  have hinflate := congrFun
    (adaptiveSmithInflateSection_integralSection_eq
      W (zeroPolynomialSection (K := K)) hdiv) i
  have hpow : (Polynomial.X : Polynomial K) ^ W i ≠ 0 :=
    pow_ne_zero _ Polynomial.X_ne_zero
  have hz :
      integralAdaptiveSmithSection W
          (zeroPolynomialSection (K := K)) hdiv i = 0 := by
    apply (mul_eq_zero.mp ?_).resolve_left hpow
    simpa [adaptiveSmithInflateSection, zeroPolynomialSection] using hinflate
  simpa [zeroPolynomialSection] using hz

/-- An integral pullback through a weight whose longitudinal coordinate is
zero preserves the longitudinal special value. -/
theorem integralAdaptiveSmithSection_special_zero_eq
    (W : Fin 4 → ℕ)
    (b : Fin 4 → Polynomial K)
    (hdiv : HasIntegralAdaptiveSmithSection W b)
    (hW0 : W (0 : Fin 4) = 0) :
    polynomialSectionSpecialPoint
        (integralAdaptiveSmithSection W b hdiv) (0 : Fin 4) =
      polynomialSectionSpecialPoint b (0 : Fin 4) := by
  have hinflate := congrFun
    (adaptiveSmithInflateSection_integralSection_eq W b hdiv) (0 : Fin 4)
  have heq :
      integralAdaptiveSmithSection W b hdiv (0 : Fin 4) =
        b (0 : Fin 4) := by
    simpa [adaptiveSmithInflateSection, hW0] using hinflate
  simp only [polynomialSectionSpecialPoint]
  rw [heq]

/-- **A19.31 same-scale geometric re-entry.**

A strict early positive Rees frontier is already an honest source-scale
exposure.  After the canonical determinant-one pointed shear it becomes a
complete `ScaleAwareAdaptiveGeometricRestartState` at the same scale and
repair tag, with raw clock `Delta - r`.

The theorem returns concrete state data and the strict raw inequality only. It
does not call the termination trace and does not declare another recursive
relation. -/
theorem
    ScaleAwareAdaptiveGeometricRestartState.exists_canonicalPositiveTransverseRees_unramifiedReentry
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hpositive : 0 < source.rawDefect)
    (hbound : HasCanonicalPositiveTransverseReesCoefficientBound
      source.rawDefect source.family)
    (hlt : canonicalPositiveTransverseSectionFrontierWeight
      source.rawDefect source.movingSection < source.rawDefect) :
    ∃ target : ScaleAwareAdaptiveGeometricRestartState (K := K),
      target.rawDefect =
          source.rawDefect -
            canonicalPositiveTransverseSectionFrontierWeight
              source.rawDefect source.movingSection ∧
      target.scale = source.scale ∧
      target.degreeCap = source.degreeCap ∧
      target.sourceComplexity = source.sourceComplexity ∧
      target.repair = source.repair ∧
      target.rawDefect < source.rawDefect := by
  let r := canonicalPositiveTransverseSectionFrontierWeight
    source.rawDefect source.movingSection
  rcases canonicalPositiveTransverseSectionFrontierWeight_even_of_lt
      (K := K) source.rawDefect source.movingSection hlt with ⟨s, hrs0⟩
  have hrs : r = 2 * s := by
    simpa [r, two_mul] using hrs0
  let W := canonicalPositiveTransverseReesWeight s
  let hint : HasIntegralAdaptiveSmithExposure 1 W r source.family :=
    canonicalPositiveTransverseRees_half_integralExposure
      (K := K) hbound (Nat.le_of_lt hlt) hrs
  let hzeroDiv : HasIntegralAdaptiveSmithSection
      W (zeroPolynomialSection (K := K)) := by
    simpa [W] using
      canonicalPositiveTransverseRees_half_zero_hasIntegralSection
        (K := K) s
  let hmoveDiv : HasIntegralAdaptiveSmithSection W source.movingSection := by
    simpa [W, r] using
      canonicalPositiveTransverseRees_half_hasIntegralSection
        (K := K) source.rawDefect s source.movingSection hrs
  let left := integralAdaptiveSmithSection W
    (zeroPolynomialSection (K := K)) hzeroDiv
  let right := integralAdaptiveSmithSection W source.movingSection hmoveDiv
  let exposed := adaptiveSmithExposureFamily 1 W r source.family hint
  let sheared := pointedBoundaryShearFamily right exposed
  let moved := pointedBoundarySequentialUnshearSection right

  have hleft : left = zeroPolynomialSection (K := K) := by
    simpa [left] using
      integralAdaptiveSmithSection_zero_eq (K := K) W hzeroDiv

  have hcollRam :
      HasPolynomialFamilyExactGradientCollision
        (parameterRamificationFamily (K := K) 1 source.family)
        (zeroPolynomialSection (K := K)) source.movingSection := by
    simpa [zeroPolynomialSection] using source.exactCollision
  have hcollExposed :
      HasPolynomialFamilyExactGradientCollision
        exposed (zeroPolynomialSection (K := K)) right := by
    have h := polynomialFamilyExactGradientCollision_adaptiveSmithExposure
      1 W r (by norm_num) source.family hint
      (zeroPolynomialSection (K := K)) source.movingSection
      hzeroDiv hmoveDiv hcollRam
    simpa [exposed, left, right, hleft] using h
  have hcollSheared :
      HasPolynomialFamilyExactGradientCollision
        sheared (zeroPolynomialSection (K := K)) moved := by
    simpa [sheared, moved] using
      polynomialFamilyExactGradientCollision_pointedBoundaryShear
        exposed right hcollExposed

  have hright0 :
      polynomialSectionSpecialPoint right (0 : Fin 4) = 1 := by
    have hpres := integralAdaptiveSmithSection_special_zero_eq
      (K := K) W source.movingSection hmoveDiv (by
        simp [W, canonicalPositiveTransverseReesWeight])
    have hsource0 := congrFun source.sectionSpecial (0 : Fin 4)
    rw [hpres]
    simpa [polynomialSectionSpecialPoint, coordinateAxisPoint] using hsource0
  have hmovedSpecial :
      polynomialSectionSpecialPoint moved =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    simpa [moved] using
      pointedBoundarySequentialUnshearSection_special_eq_axis right hright0

  have hdefExposed :
      HasPolynomialFamilyHessianDefect (K := K)
        exposed (source.rawDefect - r) := by
    simpa [exposed, hint, W, r] using
      canonicalPositiveTransverseRees_unramifiedFrontier_hessianDefect
        (K := K) source.family source.hessianDefect hbound
        (Nat.le_of_lt hlt) hrs
  have hdefSheared :
      HasPolynomialFamilyHessianDefect (K := K)
        sheared (source.rawDefect - r) := by
    simpa [sheared] using
      hessianDefect_pointedBoundaryShearFamily
        (source.rawDefect - r) right exposed hdefExposed

  have hdegreeExposed : NonlinearDegreeBound source.degreeCap exposed := by
    simpa [exposed] using
      nonlinearDegreeBound_adaptiveSmithExposureFamily
        source.degreeCap 1 r W source.family hint source.nonlinearDegreeBound
  have hdegreeSheared : NonlinearDegreeBound source.degreeCap sheared := by
    simpa [sheared] using
      nonlinearDegreeBound_pointedBoundaryShearFamily
        source.degreeCap right exposed hdegreeExposed

  let target : ScaleAwareAdaptiveGeometricRestartState (K := K) := {
    rawDefect := source.rawDefect - r
    scale := source.scale
    scale_pos := source.scale_pos
    degreeCap := source.degreeCap
    sourceComplexity := source.sourceComplexity
    repair := source.repair
    family := sheared
    movingSection := moved
    hessianDefect := hdefSheared
    nonlinearDegreeBound := hdegreeSheared
    exactCollision := by
      simpa [zeroPolynomialSection] using hcollSheared
    sectionSpecial := hmovedSpecial
  }
  have hrpos : 0 < r := by
    simpa [r] using
      source.canonicalPositiveTransverseSectionFrontierWeight_pos hpositive
  refine ⟨target, rfl, rfl, rfl, rfl, rfl, ?_⟩
  dsimp [target]
  omega

end

end HC4.Valuation
