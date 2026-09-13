import HC4.Valuation.AdaptiveAlignedSmithNoWallUnramifiedFactor
import Mathlib.Tactic

/-!
# A18.4.58: positive no-wall primitive order is same-scale defect descent

A18.4.57 removes the last reason to interpret the no-wall primitive endpoint
through a rational scaled defect.  The lower Smith family exists directly on
the incoming parameter scale and contains `X^m`.  Removing that factor gives
exact Hessian defect

    Delta - 4*m.

The transformed marked section is still the original axial right section, so
this quotient is itself a complete scale-aware adaptive restart state.  When
`m > 0`, the ordinary natural raw defect strictly decreases at *unchanged*
scale.  This is exactly the fixed-scale induction edge we wanted.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithNoWallUnramifiedSmithData

/-- In the no-wall case the lower Smith inverse source change fixes the axial
right section exactly. -/
theorem smithRightSection_eq
    {degreeCap Delta m : ℕ}
    {P : MvPolynomial (Fin 4) (Polynomial K)}
    {b : Fin 4 → Polynomial K}
    (D : AdaptiveAlignedSmithNoWallUnramifiedSmithData
      degreeCap Delta m P b) :
    D.smithRightSection = b := by
  funext i
  have hinflate := congrFun
    (smithConformalInflateSection_integralSection_eq
      m m b D.rightSectionDivisibility) i
  change
    smithConformalDerivativeCoefficient (K := K) m m i *
        D.smithRightSection i = b i at hinflate
  by_cases hi : i = (0 : Fin 4)
  · subst i
    simpa [smithConformalDerivativeCoefficient,
      smithConformalSourceExponent] using hinflate
  · have hbzero :=
      rightTransverse_zero_of_noGenuineWall
        P (zeroPolynomialSection (K := K)) b D.noWall i hi
    rw [hbzero] at hinflate ⊢
    have hcoeff :
        smithConformalDerivativeCoefficient (K := K) m m i ≠ 0 := by
      unfold smithConformalDerivativeCoefficient
      exact pow_ne_zero _ Polynomial.X_ne_zero
    exact (mul_eq_zero.mp hinflate).resolve_left hcoeff

end AdaptiveAlignedSmithNoWallUnramifiedSmithData

/-- Geometry-bearing same-scale restart produced by positive minimal no-wall
parameter order. -/
structure AdaptiveAlignedSmithCanonicalNoWallDefectDrop
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K)) : Type (u + 1) where
  primitive : AdaptiveAlignedSmithNoWallUnramifiedPrimitiveData
    source.degreeCap source.rawDefect
    (zeroJetNormalizedFamily source.family) source.movingSection
  m_pos : 0 < primitive.m
  target : ScaleAwareAdaptiveGeometricRestartState (K := K)
  target_eq_raw : target.rawDefect = source.rawDefect - 4 * primitive.m
  target_eq_scale : target.scale = source.scale
  progress : CertifiedSameScaleEpisodeProgress RR target source

namespace ScaleAwareAdaptiveGeometricRestartState

/-- The actual lower-scale quotient state attached to one no-wall primitive
package. -/
noncomputable def noWallUnramifiedPrimitiveTarget
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (D : AdaptiveAlignedSmithNoWallUnramifiedPrimitiveData
      source.degreeCap source.rawDefect
      (zeroJetNormalizedFamily source.family) source.movingSection) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) := by
  have hright : D.smithData.smithRightSection = source.movingSection :=
    D.smithData.smithRightSection_eq
  exact {
    rawDefect := source.rawDefect - 4 * D.m
    scale := source.scale
    scale_pos := source.scale_pos
    degreeCap := source.degreeCap
    sourceComplexity := source.sourceComplexity
    repair := source.repair
    family := D.reducedFamily
    movingSection := source.movingSection
    hessianDefect := D.reducedFamily_hessianDefect
    nonlinearDegreeBound := D.reducedFamily_nonlinearDegreeBound
    exactCollision := by
      simpa [hright] using D.reducedFamily_exactCollision
    sectionSpecial := source.sectionSpecial
  }

@[simp]
theorem noWallUnramifiedPrimitiveTarget_rawDefect
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (D : AdaptiveAlignedSmithNoWallUnramifiedPrimitiveData
      source.degreeCap source.rawDefect
      (zeroJetNormalizedFamily source.family) source.movingSection) :
    (source.noWallUnramifiedPrimitiveTarget D).rawDefect =
      source.rawDefect - 4 * D.m := rfl

@[simp]
theorem noWallUnramifiedPrimitiveTarget_scale
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (D : AdaptiveAlignedSmithNoWallUnramifiedPrimitiveData
      source.degreeCap source.rawDefect
      (zeroJetNormalizedFamily source.family) source.movingSection) :
    (source.noWallUnramifiedPrimitiveTarget D).scale = source.scale := rfl

/-- Positive minimal no-wall order is a literal strict raw-defect decrease at
unchanged parameter scale. -/
theorem noWallUnramifiedPrimitive_sameScaleProgress
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (D : AdaptiveAlignedSmithNoWallUnramifiedPrimitiveData
      source.degreeCap source.rawDefect
      (zeroJetNormalizedFamily source.family) source.movingSection)
    (hm : 0 < D.m) :
    CertifiedSameScaleEpisodeProgress RR
      (source.noWallUnramifiedPrimitiveTarget D) source := by
  have hle : 4 * D.m ≤ source.rawDefect :=
    four_mul_le_defect_of_commonParameterFactor
      D.m D.smithData.smithFamily D.commonFactor source.rawDefect
      D.smithData.smithFamily_hessianDefect
  have hlt : source.rawDefect - 4 * D.m < source.rawDefect := by
    omega
  exact certifiedSameScaleEpisodeProgress_of_rawDefect_lt
    (K := K) RR (by rfl) (by simpa using hlt)

/-- Canonical positive-`m` no-wall defect-drop package from the incoming
normalized family. -/
noncomputable def noWallDefectDrop
    (RR : RepairRanking)
    (source : ScaleAwareAdaptiveGeometricRestartState (K := K))
    (hnone :
      ¬ HasAlignedSmithGenuineWall
        (zeroJetNormalizedFamily source.family)
        (zeroPolynomialSection (K := K)) source.movingSection)
    (hm :
      0 < (AdaptiveAlignedSmithNoWallUnramifiedPrimitiveData.ofNoWall
        source.degreeCap source.rawDefect
        (zeroJetNormalizedFamily source.family) source.movingSection
        hnone source.normalized_hessianDefect
        source.normalized_nonlinearDegreeBound
        source.normalized_exactCollision source.sectionSpecial).m) :
    AdaptiveAlignedSmithCanonicalNoWallDefectDrop RR source := by
  let D := AdaptiveAlignedSmithNoWallUnramifiedPrimitiveData.ofNoWall
    source.degreeCap source.rawDefect
    (zeroJetNormalizedFamily source.family) source.movingSection
    hnone source.normalized_hessianDefect
    source.normalized_nonlinearDegreeBound
    source.normalized_exactCollision source.sectionSpecial
  let target := source.noWallUnramifiedPrimitiveTarget D
  exact {
    primitive := D
    m_pos := by simpa [D] using hm
    target := target
    target_eq_raw := rfl
    target_eq_scale := rfl
    progress := source.noWallUnramifiedPrimitive_sameScaleProgress
      RR D (by simpa [D] using hm)
  }

end ScaleAwareAdaptiveGeometricRestartState

end

end HC4.Valuation
