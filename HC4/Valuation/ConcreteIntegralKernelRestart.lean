import HC4.Valuation.IntegralKernelBlowup
import HC4.Valuation.PolynomialFamilyKernelRestart
import Mathlib.Tactic

/-!
# Concrete integral kernel restart

Phases 93.52--93.54 construct the integral kernel blow-up and prove exact
family-gradient collision covariance.

Phase 93.51 proves that any polynomial family carrying an exact marked
collision, distinct special points, and a positive defect drop yields a
strict global restart.

This file joins those two layers with no new geometric hypothesis.

For positive slope, the concrete integral blow-up therefore gives:

* an exact gradient collision on the transformed family;
* an exact collision on the special fibre;
* strict determinant-defect decrease;
* `GlobalRestartProgress`;
* an immediate contradiction under JC2 if the special fibre is terminal.

For slope zero, the explicit coefficient construction is literally the
identity polynomial and the moving-section transformation is literally the
identity section.  Thus zero slope is not a restart; it belongs to the local
special-fibre classifier.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Zero slope is the identity -/

/-- At slope zero, the explicitly reconstructed integral blow-up polynomial
is exactly the original polynomial family. -/
theorem integralKernelBlowupFamily_zero_eq
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel 0 P) :
    integralKernelBlowupFamily kernel 0 P hdiv = P := by
  apply MvPolynomial.ext
  intro d
  exact
    (integralKernelBlowupFamily_coeff_slope_zero
      kernel P hdiv d).symm

/-- The whole concrete kernel blow-up operation is the identity at slope
zero: both the polynomial family and every moving marked section are
unchanged. -/
theorem integralKernelBlowup_zero_is_identity
    (kernel : Fin 4)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel 0 P)
    (a : Fin 4 → Polynomial K) :
    integralKernelBlowupFamily kernel 0 P hdiv = P ∧
      kernelBlowupSection kernel 0 a = a := by
  exact
    ⟨integralKernelBlowupFamily_zero_eq
        kernel P hdiv,
      kernelBlowupSection_zero kernel a⟩

/-! ## Positive-slope special-point normalisation -/

/-- If the original moving section reduces to the origin, then after every
positive-slope kernel blow-up its reduction is still the origin.

The kernel coordinate vanishes because it acquires a positive power of
`τ`; every non-kernel coordinate is unchanged. -/
theorem polynomialSectionSpecialPoint_kernelBlowupSection_eq_zero
    (kernel : Fin 4)
    {slope : ℕ}
    (hslope : 0 < slope)
    (a : Fin 4 → Polynomial K)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K))) :
    polynomialSectionSpecialPoint
        (kernelBlowupSection kernel slope a) =
      (fun _ => (0 : K)) := by
  funext i
  by_cases hi : i = kernel
  · subst i
    exact
      polynomialSectionSpecialPoint_kernelBlowupSection_kernel
        kernel hslope a
  · rw [
      polynomialSectionSpecialPoint_kernelBlowupSection_of_ne
        kernel slope a hi]
    exact congrFun ha i

/-! ## Concrete positive-slope restart certificate -/

/-- **The concrete integral blow-up constructs the Phase 93.51 restart
certificate.**

No family-collision field is assumed for the transformed polynomial: it is
proved automatically by the Phase 93.54 derivative-covariance theorem. -/
theorem integralKernelBlowup_toPolynomialFamilyKernelRestartCertificate
    {s t : GlobalRestartState}
    (kernel : Fin 4)
    (slope : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (a b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (hspecialDistinct :
      polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope a) ≠
        polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope b))
    (hdrop :
      HasPositiveKernelDefectDrop slope s t) :
    PolynomialFamilyKernelRestartCertificate
      s t slope
      (integralKernelBlowupFamily
        kernel slope P hdiv)
      (kernelBlowupSection kernel slope a)
      (kernelBlowupSection kernel slope b) := by
  exact
    { familyCollision :=
        polynomialFamilyExactGradientCollision_integralKernelBlowup
          kernel slope P hdiv a b hcoll
      specialPointsDistinct := hspecialDistinct
      positiveDefectDrop := hdrop }

/-- **End-to-end positive-slope kernel restart.**

Starting from the concrete coefficient-divisibility condition and an exact
family collision, the integral kernel blow-up produces a distinct exact
special-fibre collision and a strict global restart step. -/
theorem integralKernelBlowup_preservesSpecialCollision_and_strictlyRestarts
    {s t : GlobalRestartState}
    (kernel : Fin 4)
    (slope : ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (a b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (hspecialDistinct :
      polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope a) ≠
        polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope b))
    (hdrop :
      HasPositiveKernelDefectDrop slope s t) :
    polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope a) ≠
        polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope b) ∧
      HasExactGradientCollision
        (polynomialFamilySpecialFiber
          (integralKernelBlowupFamily
            kernel slope P hdiv))
        (polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope a))
        (polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope b)) ∧
      t.defect < s.defect ∧
      GlobalRestartProgress s t := by
  exact
    polynomialFamilyKernelRestart_preservesCollision_and_strictlyRestarts
      (integralKernelBlowup_toPolynomialFamilyKernelRestartCertificate
        kernel slope P hdiv a b
        hcoll hspecialDistinct hdrop)

/-! ## Pointed positive-slope restart -/

/-- The concrete positive-slope blow-up also constructs the pointed restart
certificate when the first original section reduces to the origin.

The second pointed target is chosen canonically to be the reduction of the
transformed second moving section. -/
theorem integralKernelBlowup_toPointedPolynomialFamilyKernelRestartCertificate
    {s t : GlobalRestartState}
    (kernel : Fin 4)
    {slope : ℕ}
    (hslope : 0 < slope)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (a b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hspecialDistinct :
      polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope a) ≠
        polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope b))
    (hdrop :
      HasPositiveKernelDefectDrop slope s t) :
    PointedPolynomialFamilyKernelRestartCertificate
      s t slope
      (integralKernelBlowupFamily
        kernel slope P hdiv)
      (kernelBlowupSection kernel slope a)
      (kernelBlowupSection kernel slope b)
      (polynomialSectionSpecialPoint
        (kernelBlowupSection kernel slope b)) := by
  have ha' :
      polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope a) =
        (fun _ => (0 : K)) :=
    polynomialSectionSpecialPoint_kernelBlowupSection_eq_zero
      kernel hslope a ha
  exact
    { familyCollision :=
        polynomialFamilyExactGradientCollision_integralKernelBlowup
          kernel slope P hdiv a b hcoll
      firstSpecialPoint := ha'
      secondSpecialPoint := rfl
      secondPointNonzero := by
        intro hb0
        apply hspecialDistinct
        rw [ha', hb0]
      positiveDefectDrop := hdrop }

/-- **Pointed end-to-end positive-slope restart.**

The transformed special fibre has an exact collision from the origin to the
canonical nonzero second reduction, while determinant defect drops
strictly. -/
theorem integralKernelBlowup_pointedZeroCollision_and_strictlyRestarts
    {s t : GlobalRestartState}
    (kernel : Fin 4)
    {slope : ℕ}
    (hslope : 0 < slope)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (a b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hspecialDistinct :
      polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope a) ≠
        polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope b))
    (hdrop :
      HasPositiveKernelDefectDrop slope s t) :
    polynomialSectionSpecialPoint
        (kernelBlowupSection kernel slope b) ≠
          (fun _ => (0 : K)) ∧
      HasExactGradientCollision
        (polynomialFamilySpecialFiber
          (integralKernelBlowupFamily
            kernel slope P hdiv))
        (fun _ => (0 : K))
        (polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope b)) ∧
      t.defect < s.defect ∧
      GlobalRestartProgress s t := by
  exact
    pointedPolynomialFamilyKernelRestart_zeroCollision_and_strictlyRestarts
      (integralKernelBlowup_toPointedPolynomialFamilyKernelRestartCertificate
        kernel hslope P hdiv a b
        hcoll ha hspecialDistinct hdrop)

/-! ## Terminal special fibre under JC2 -/

section Terminal

variable [CharZero K]

/-- **A concrete positive-slope integral kernel blow-up cannot land in a
certified terminal endpoint under JC2.**

This is the positive-slope terminal branch of the eventual global
`JC2ImpliesHC4` dispatcher. -/
theorem integralKernelBlowup_terminalSpecialFiber_impossible_of_JC2
    (hJC2 : HC4.PlanarJC2Injectivity K)
    {s t : GlobalRestartState}
    (kernel : Fin 4)
    {slope : ℕ}
    (hslope : 0 < slope)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (hdiv :
      HasIntegralKernelCoefficientDivisibility
        kernel slope P)
    (a b : Fin 4 → Polynomial K)
    (hcoll :
      HasPolynomialFamilyExactGradientCollision
        P a b)
    (ha :
      polynomialSectionSpecialPoint a =
        (fun _ => (0 : K)))
    (hspecialDistinct :
      polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope a) ≠
        polynomialSectionSpecialPoint
          (kernelBlowupSection kernel slope b))
    (hdrop :
      HasPositiveKernelDefectDrop slope s t)
    (hterminal :
      CertifiedTerminalEndpoint
        (polynomialFamilySpecialFiber
          (integralKernelBlowupFamily
            kernel slope P hdiv))) :
    False := by
  exact
    pointedPolynomialFamilyKernelRestart_terminalSpecialFiber_impossible_of_JC2
      hJC2
      (integralKernelBlowup_toPointedPolynomialFamilyKernelRestartCertificate
        kernel hslope P hdiv a b
        hcoll ha hspecialDistinct hdrop)
      hterminal

end Terminal

end

end HC4.Valuation
