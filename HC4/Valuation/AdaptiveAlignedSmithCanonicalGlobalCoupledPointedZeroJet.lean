import HC4.Valuation.AdaptiveAlignedSmithCanonicalGlobalCoupledMinimalPresentation
import HC4.Valuation.AdaptiveAlignedSmithBoundaryReentry
import Mathlib.Tactic

/-!
# A18.4.19: zero-jet canonical pointed presentation of a coupled wall

A18.4.18 shows that the residual coupled wall is already a nonprimitive,
symmetric-minimal coefficient wall and that every monomial on its actual
first-wall special fibre has negative symmetric Smith derivative.  The only
noncanonical datum is the right marked special point produced by the
simultaneous section wall.

The repository already contains the correct determinant-one three-shear
normalisation of such a marked point.  This file proves the one missing
invariant for using that normalisation directly in the raw canonical Smith
classifier: a linear transverse source shear preserves `HasZeroSourceJet`.
Consequently the complete three-shear pointed boundary normalisation preserves
the zero source jet as well.

We then package the coupled first-wall family after the existing pointed
boundary shear with its exact Hessian clock, nonlinear degree cap, exact
zero-left collision, restored right special point `e0`, and zero-source-jet
provenance.  No homogeneity assumption is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-! ## Linear shears preserve the zero source jet -/

/-- An elementary determinant-one transverse source shear preserves the
vanishing source constant and linear coefficients. -/
theorem HasZeroSourceJet.elementaryShearHom
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    (hP : HasZeroSourceJet P)
    (k : Fin 4)
    (hk0 : k ≠ (0 : Fin 4))
    (c : Polynomial K) :
    HasZeroSourceJet (elementaryShearHom (K := K) k c P) := by
  let z : Fin 4 → Polynomial K := zeroPolynomialSection (K := K)
  have hshearEvalZero :
      ∀ Q : MvPolynomial (Fin 4) (Polynomial K),
        MvPolynomial.eval z Q = 0 →
          MvPolynomial.eval z
            (elementaryShearHom (K := K) k c Q) = 0 := by
    intro Q hQ
    have hcov :=
      eval_elementaryShearHom_unshear
        (K := K) k hk0 c Q z
    have hz : elementaryUnshearSection k c z = z := by
      simpa [z] using elementaryUnshearSection_zero (K := K) k c
    rw [hz] at hcov
    rw [hcov]
    exact hQ
  refine ⟨?_, ?_⟩
  · have hP0 : MvPolynomial.eval z P = 0 := by
      simpa [z, zeroPolynomialSection] using hP.valueAtZero
    have hout := hshearEvalZero P hP0
    change
      MvPolynomial.eval
          (fun _ : Fin 4 => (0 : Polynomial K))
          (elementaryShearHom (K := K) k c P) = 0 at hout
    rw [MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq] at hout
    exact hout
  · intro i
    have hinput :
        ∀ j : Fin 4,
          MvPolynomial.eval z (MvPolynomial.pderiv j P) = 0 := by
      intro j
      simpa [z, zeroPolynomialSection] using hP.gradientAtZero j
    have hgrad :
        MvPolynomial.eval z
          (MvPolynomial.pderiv i
            (elementaryShearHom (K := K) k c P)) = 0 := by
      by_cases hi0 : i = (0 : Fin 4)
      · subst i
        rw [pderiv_zero_elementaryShearHom
          (K := K) k hk0 c P]
        have h0 :=
          hshearEvalZero
            (MvPolynomial.pderiv (0 : Fin 4) P)
            (hinput (0 : Fin 4))
        have hk :=
          hshearEvalZero
            (MvPolynomial.pderiv k P)
            (hinput k)
        simp [h0, hk]
      · rw [pderiv_elementaryShearHom_of_ne_zero
          (K := K) k hk0 c i hi0 P]
        exact
          hshearEvalZero
            (MvPolynomial.pderiv i P)
            (hinput i)
    change
      MvPolynomial.eval
          (fun _ : Fin 4 => (0 : Polynomial K))
          (MvPolynomial.pderiv i
            (elementaryShearHom (K := K) k c P)) = 0 at hgrad
    rw [MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq] at hgrad
    rw [coeff_pderiv_mixedDegree
      (K := Polynomial K) i
      (elementaryShearHom (K := K) k c P)
      (0 : Fin 4 →₀ ℕ)] at hgrad
    simpa using hgrad

/-- The canonical three-shear boundary normalisation therefore preserves a
zero source jet. -/
theorem HasZeroSourceJet.pointedBoundaryShearFamily
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    (hP : HasZeroSourceJet P)
    (b : Fin 4 → Polynomial K) :
    HasZeroSourceJet (pointedBoundaryShearFamily b P) := by
  unfold pointedBoundaryShearFamily
  exact
    (((hP.elementaryShearHom
        (1 : Fin 4) (by decide)
        (pointedBoundaryShearPolynomialCoefficient b (1 : Fin 4))).
      elementaryShearHom
        (2 : Fin 4) (by decide)
        (pointedBoundaryShearPolynomialCoefficient b (2 : Fin 4))).
      elementaryShearHom
        (3 : Fin 4) (by decide)
        (pointedBoundaryShearPolynomialCoefficient b (3 : Fin 4))

/-! ## Coupled pointed data -/

/-- The literal first-wall family carried by a coupled presentation. -/
noncomputable def AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.firstWallFamily
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation (K := K) s) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  alignedSmithGenuineFirstWallFamily
    (K := K)
    (zeroJetNormalizedFamily s.family)
    (zeroPolynomialSection (K := K))
    s.movingSection P.boundary.hwall

/-- The literal transformed right section at the same coupled first wall. -/
noncomputable def AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.firstWallRightSection
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation (K := K) s) :
    Fin 4 → Polynomial K :=
  alignedSmithGenuineFirstWallSectionRight
    (zeroJetNormalizedFamily s.family)
    (zeroPolynomialSection (K := K))
    s.movingSection P.boundary.hwall

/-- Pointed determinant-one normalisation of the coupled first-wall family. -/
noncomputable def AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.pointedFamily
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation (K := K) s) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  pointedBoundaryShearFamily P.firstWallRightSection P.firstWallFamily

/-- Canonically unsheared right section paired with `pointedFamily`. -/
noncomputable def AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.pointedSection
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation (K := K) s) :
    Fin 4 → Polynomial K :=
  pointedBoundarySequentialUnshearSection P.firstWallRightSection

/-- The pointed coupled family retains the exact aligned-wall Hessian clock. -/
theorem AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.pointedFamily_hessianDefect
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation (K := K) s) :
    HasPolynomialFamilyHessianDefect
      (K := K) P.pointedFamily
      (alignedSmithRamificationIndex * s.rawDefect) := by
  unfold AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.pointedFamily
    AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.firstWallFamily
  exact
    hessianDefect_pointedBoundaryShearFamily
      (alignedSmithRamificationIndex * s.rawDefect)
      P.firstWallRightSection
      (alignedSmithGenuineFirstWallFamily
        (K := K)
        (zeroJetNormalizedFamily s.family)
        (zeroPolynomialSection (K := K))
        s.movingSection P.boundary.hwall)
      P.boundary.hessianDefect

/-- The nonlinear source-degree ceiling survives the pointed coupled shear. -/
theorem AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.pointedFamily_degreeBound
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation (K := K) s) :
    NonlinearDegreeBound s.degreeCap P.pointedFamily := by
  unfold AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.pointedFamily
    AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.firstWallFamily
  exact
    nonlinearDegreeBound_pointedBoundaryShearFamily
      s.degreeCap P.firstWallRightSection
      (alignedSmithGenuineFirstWallFamily
        (K := K)
        (zeroJetNormalizedFamily s.family)
        (zeroPolynomialSection (K := K))
        s.movingSection P.boundary.hwall)
      P.boundary.nonlinearDegreeBound

/-- The exact zero-left collision is covariant under the pointed coupled
source change. -/
theorem AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.pointedFamily_exactCollision
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation (K := K) s) :
    HasPolynomialFamilyExactGradientCollision
      P.pointedFamily
      (zeroPolynomialSection (K := K))
      P.pointedSection := by
  unfold AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.pointedFamily
    AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.pointedSection
    AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.firstWallFamily
    AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.firstWallRightSection
  exact
    polynomialFamilyExactGradientCollision_pointedBoundaryShear
      (alignedSmithGenuineFirstWallFamily
        (K := K)
        (zeroJetNormalizedFamily s.family)
        (zeroPolynomialSection (K := K))
        s.movingSection P.boundary.hwall)
      (alignedSmithGenuineFirstWallSectionRight
        (zeroJetNormalizedFamily s.family)
        (zeroPolynomialSection (K := K))
        s.movingSection P.boundary.hwall)
      P.boundary.exactCollision

/-- The simultaneous right-section wall is removed at the level of the marked
special point: the pointed right section is exactly based at `e0`. -/
theorem AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.pointedSection_special
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation (K := K) s) :
    polynomialSectionSpecialPoint P.pointedSection =
      coordinateAxisPoint (K := K) (0 : Fin 4) := by
  unfold AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.pointedSection
    AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.firstWallRightSection
  apply pointedBoundarySequentialUnshearSection_special_eq_axis
  exact
    alignedSmithGenuineFirstWallSectionRight_special_zero
      (zeroJetNormalizedFamily s.family)
      s.movingSection P.boundary.hwall s.sectionSpecial

/-- Most importantly for direct raw-special-fibre classification, pointed
normalisation does not force a second zero-jet subtraction. -/
theorem AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.pointedFamily_zeroSourceJet
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation (K := K) s) :
    HasZeroSourceJet P.pointedFamily := by
  unfold AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.pointedFamily
  exact
    P.zeroSourceJet.pointedBoundaryShearFamily P.firstWallRightSection

/-- Complete pointed coupled presentation except for the one remaining
special-fibre statement: symmetric minimality after the triangular shear. -/
structure AdaptiveAlignedSmithCanonicalCoupledPointedPresentation
    (s : ScaleAwareAdaptiveGeometricRestartState (K := K)) where
  source : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation (K := K) s
  hessianDefect :
    HasPolynomialFamilyHessianDefect
      (K := K) source.pointedFamily
      (alignedSmithRamificationIndex * s.rawDefect)
  nonlinearDegreeBound : NonlinearDegreeBound s.degreeCap source.pointedFamily
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      source.pointedFamily
      (zeroPolynomialSection (K := K))
      source.pointedSection
  sectionSpecial :
    polynomialSectionSpecialPoint source.pointedSection =
      coordinateAxisPoint (K := K) (0 : Fin 4)
  zeroSourceJet : HasZeroSourceJet source.pointedFamily

/-- Every coupled minimal presentation canonically supplies all pointed data
except the final symmetric-minimality transport. -/
noncomputable def AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation.toPointedPresentation
    {s : ScaleAwareAdaptiveGeometricRestartState (K := K)}
    (P : AdaptiveAlignedSmithCanonicalCoupledMinimalPresentation (K := K) s) :
    AdaptiveAlignedSmithCanonicalCoupledPointedPresentation (K := K) s :=
  { source := P
    hessianDefect := P.pointedFamily_hessianDefect
    nonlinearDegreeBound := P.pointedFamily_degreeBound
    exactCollision := P.pointedFamily_exactCollision
    sectionSpecial := P.pointedSection_special
    zeroSourceJet := P.pointedFamily_zeroSourceJet }

end

end HC4.Valuation
