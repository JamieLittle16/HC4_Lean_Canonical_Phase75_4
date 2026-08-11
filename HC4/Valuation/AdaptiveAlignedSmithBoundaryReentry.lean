import HC4.Valuation.AdaptiveSectionBoundaryReentry
import HC4.Valuation.AdaptiveAlignedSmithClassifierDispatcher
import Mathlib.Tactic

/-!
# Re-entry of the original aligned-Smith section boundary

The one-shot aligned-Smith macro has a top-level section-boundary output.
It already carries the actual transformed family, its exact Hessian clock,
the nonlinear degree cap, and an exact zero-left collision.  The only datum
not stored explicitly is that the transformed right section still has
longitudinal special coordinate `1`.

That fact is formal and independent of the boundary mechanism:

* coordinate `0` has zero Smith source exponent;
* integral Smith section division therefore leaves coordinate `0` unchanged;
* positive parameter ramification preserves the constant coefficient.

Once this is recorded, the determinant-one pointed boundary shear developed
for coefficientwise Smith exposure applies verbatim.  Hence the original
aligned section boundary also re-enters the ordinary adaptive state space.

No progress/decrease assertion is made here.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-! ## Coordinate zero is untouched by integral Smith section division -/

/-- The longitudinal coordinate of an integral Smith-conformal section is
unchanged.  This is proved from the inflation/deflation identity, avoiding
any dependent `Classical.choose` manipulation. -/
theorem integralSmithConformalSection_zero_eq
    (A B : ℕ)
    (c : Fin 4 → Polynomial K)
    (hdiv :
      HasIntegralSmithConformalSectionDivisibility
        A B c) :
    integralSmithConformalSection A B c hdiv (0 : Fin 4) =
      c (0 : Fin 4) := by
  have hreinflate :=
    congrFun
      (smithConformalInflateSection_integralSection_eq
        (K := K) A B c hdiv)
      (0 : Fin 4)
  simpa [smithConformalInflateSection,
    smithConformalDerivativeCoefficient,
    smithConformalSourceExponent] using hreinflate

/-- Coordinate zero of the genuine aligned first-wall right section is just
coordinate zero of the ramified input section. -/
theorem alignedSmithGenuineFirstWallSectionRight_zero_eq
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (a b : Fin 4 → Polynomial K)
    (hwall : HasAlignedSmithGenuineWall P a b) :
    alignedSmithGenuineFirstWallSectionRight
        P a b hwall (0 : Fin 4) =
      parameterRamificationSection
        (K := K) alignedSmithRamificationIndex b (0 : Fin 4) := by
  unfold alignedSmithGenuineFirstWallSectionRight
  apply integralSmithConformalSection_zero_eq

/-- Therefore a canonical incoming right section keeps longitudinal special
value `1` at a genuine aligned first wall, even when a transverse section
wall is hit. -/
theorem alignedSmithGenuineFirstWallSectionRight_special_zero
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (b : Fin 4 → Polynomial K)
    (hwall :
      HasAlignedSmithGenuineWall
        P (zeroPolynomialSection (K := K)) b)
    (hb :
      polynomialSectionSpecialPoint b =
        coordinateAxisPoint (K := K) (0 : Fin 4)) :
    polynomialSectionSpecialPoint
        (alignedSmithGenuineFirstWallSectionRight
          P (zeroPolynomialSection (K := K)) b hwall)
        (0 : Fin 4) = 1 := by
  have hramSpecial :
      polynomialSectionSpecialPoint
          (parameterRamificationSection
            (K := K) alignedSmithRamificationIndex b) =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    rw [polynomialSectionSpecialPoint_parameterRamificationSection
      alignedSmithRamificationIndex alignedSmithRamificationIndex_pos b]
    exact hb
  have hram0 := congrFun hramSpecial (0 : Fin 4)
  change
    Polynomial.constantCoeff
      (alignedSmithGenuineFirstWallSectionRight
        P (zeroPolynomialSection (K := K)) b hwall (0 : Fin 4)) = 1
  rw [alignedSmithGenuineFirstWallSectionRight_zero_eq]
  simpa [polynomialSectionSpecialPoint, coordinateAxisPoint] using hram0

/-! ## State-aware re-entry -/

/-- The aligned boundary family after the canonical determinant-one pointed
source shear. -/
noncomputable def ScaleAwareAdaptiveGeometricRestartState.alignedBoundaryShearedFamily
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (B :
      AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) s.degreeCap s.rawDefect
        (zeroJetNormalizedFamily s.family) s.movingSection) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  let F :=
    alignedSmithGenuineFirstWallFamily
      (zeroJetNormalizedFamily s.family)
      (zeroPolynomialSection (K := K))
      s.movingSection B.hwall
  let b :=
    alignedSmithGenuineFirstWallSectionRight
      (zeroJetNormalizedFamily s.family)
      (zeroPolynomialSection (K := K))
      s.movingSection B.hwall
  pointedBoundaryShearFamily b F

/-- Canonically unsheared right section attached to the same aligned
boundary. -/
noncomputable def ScaleAwareAdaptiveGeometricRestartState.alignedBoundaryUnshearedSection
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (B :
      AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) s.degreeCap s.rawDefect
        (zeroJetNormalizedFamily s.family) s.movingSection) :
    Fin 4 → Polynomial K :=
  pointedBoundarySequentialUnshearSection
    (alignedSmithGenuineFirstWallSectionRight
      (zeroJetNormalizedFamily s.family)
      (zeroPolynomialSection (K := K))
      s.movingSection B.hwall)

/-- **Original aligned-boundary re-entry.**

A top-level aligned-Smith section boundary is coordinate-removable.  After
the canonical three-shear source change it is again an ordinary adaptive
geometric restart state.

The raw Hessian clock is the genuine-wall clock
`alignedSmithRamificationIndex * s.rawDefect`; this theorem deliberately
does not claim that this is a strict global decrease. -/
noncomputable def ScaleAwareAdaptiveGeometricRestartState.alignedBoundaryReentry
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (B :
      AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) s.degreeCap s.rawDefect
        (zeroJetNormalizedFamily s.family) s.movingSection) :
    AdaptiveGeometricRestartState (K := K) := by
  let F :=
    alignedSmithGenuineFirstWallFamily
      (zeroJetNormalizedFamily s.family)
      (zeroPolynomialSection (K := K))
      s.movingSection B.hwall
  let b :=
    alignedSmithGenuineFirstWallSectionRight
      (zeroJetNormalizedFamily s.family)
      (zeroPolynomialSection (K := K))
      s.movingSection B.hwall

  have hb0 :
      polynomialSectionSpecialPoint b (0 : Fin 4) = 1 := by
    dsimp [b]
    exact
      alignedSmithGenuineFirstWallSectionRight_special_zero
        (zeroJetNormalizedFamily s.family)
        s.movingSection B.hwall s.sectionSpecial

  exact
    {
      defect := alignedSmithRamificationIndex * s.rawDefect
      degreeCap := s.degreeCap
      sourceComplexity := s.sourceComplexity
      repair := s.repair
      family := pointedBoundaryShearFamily b F
      movingSection := pointedBoundarySequentialUnshearSection b
      hessianDefect := by
        exact
          hessianDefect_pointedBoundaryShearFamily
            (alignedSmithRamificationIndex * s.rawDefect)
            b F B.hessianDefect
      nonlinearDegreeBound := by
        exact
          nonlinearDegreeBound_pointedBoundaryShearFamily
            s.degreeCap b F B.nonlinearDegreeBound
      exactCollision := by
        exact
          polynomialFamilyExactGradientCollision_pointedBoundaryShear
            F b B.exactCollision
      sectionSpecial := by
        exact
          pointedBoundarySequentialUnshearSection_special_eq_axis
            b hb0
    }

/-- The re-entry state carries exactly the genuine aligned-wall raw clock. -/
@[simp]
theorem ScaleAwareAdaptiveGeometricRestartState.alignedBoundaryReentry_defect
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (B :
      AdaptiveAlignedSmithSectionBoundaryEndpoint
        (K := K) s.degreeCap s.rawDefect
        (zeroJetNormalizedFamily s.family) s.movingSection) :
    (s.alignedBoundaryReentry B).defect =
      alignedSmithRamificationIndex * s.rawDefect := rfl

end

end HC4.Valuation
