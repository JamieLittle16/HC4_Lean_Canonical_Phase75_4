import HC4.Valuation.AdaptiveAlignedSmithCanonicalPointedCollisionRecentering
import HC4.Valuation.AdaptiveAlignedSmithTransverseSourceShear
import HC4.Valuation.PointedShearContinuation
import HC4.Valuation.NonlinearDegreeBoundPreservation
import HC4.Valuation.PolynomialFamilyHessianSpecialFiber
import Mathlib.Tactic

/-!
# A18.5.85: determinant-one axis normalisation of a pointed collision

A18.5.84 recentres an arbitrary distinct determinant-one gradient collision to
`0 ~ v` for a nonzero source vector `v`.  This file performs the remaining
linear normalisation using only determinant-one transvections already proved
source-honest in the aligned-Smith development.

There is no need for a general matrix-substitution chain rule.

* If `v_0 = 0`, choose a nonzero transverse coordinate and one transvection
  `X_0 -> X_0 + c X_i` making the inverse-transformed marked point have
  longitudinal coordinate `1`.
* If `v_0 != 0`, first use `X_1 -> X_1 + c X_0` to make the transformed
  coordinate `1` equal to `v_0`, then use `X_0 -> X_0 + c X_1` to make the
  longitudinal coordinate equal to `1`.
* The already-green three-shear pointed normalisation then kills coordinates
  `1,2,3`, leaving exactly `e_0`.

Every step preserves the pure Hessian clock, the zero-left exact collision and
the nonlinear source-degree bound.  Specialising at the parameter origin
therefore produces the exact `AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry`
consumed by A18.4.109.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace AdaptiveAlignedSmithCanonicalPointedZeroDefectCollisionEntry

/-- Intermediate family-level data after determinant-one transvections have
made the longitudinal special coordinate exactly one. -/
structure LongitudinalOneData
    (E : AdaptiveAlignedSmithCanonicalPointedZeroDefectCollisionEntry (K := K)) :
    Type (u + 1) where
  family : MvPolynomial (Fin 4) (Polynomial K)
  rightSection : Fin 4 → Polynomial K
  hessianDefect : HasPolynomialFamilyHessianDefect (K := K) family 0
  nonlinearDegreeBound : NonlinearDegreeBound E.degreeCap family
  exactCollision :
    HasPolynomialFamilyExactGradientCollision
      family (zeroPolynomialSection (K := K)) rightSection
  rightSpecialZero :
    polynomialSectionSpecialPoint rightSection (0 : Fin 4) = 1

private theorem longitudinalOneData_nonempty
    (E : AdaptiveAlignedSmithCanonicalPointedZeroDefectCollisionEntry (K := K)) :
    Nonempty (LongitudinalOneData E) := by
  let P0 := zeroDefectConstantParameterFamily E.polynomial
  let b0 := polynomialConstantSection E.endpoint

  have hdef0 : HasPolynomialFamilyHessianDefect (K := K) P0 0 := by
    simpa [P0] using
      zeroDefectConstantParameterFamily_hessianDefect
        E.polynomial E.hessian_one
  have hdegree0 : NonlinearDegreeBound E.degreeCap P0 := by
    simpa [P0] using
      zeroDefectConstantParameterFamily_nonlinearDegreeBound
        E.polynomial E.degreeCap E.nonlinearDegreeBound
  have hcoll0 :
      HasPolynomialFamilyExactGradientCollision
        P0 (zeroPolynomialSection (K := K)) b0 := by
    have h := zeroDefectConstantParameterFamily_exactCollision
      E.polynomial (fun _ : Fin 4 => (0 : K)) E.endpoint E.exactCollision
    have hzeroSection :
        polynomialConstantSection (fun _ : Fin 4 => (0 : K)) =
          zeroPolynomialSection (K := K) := by
      funext i
      simp [polynomialConstantSection, zeroPolynomialSection]
    rw [hzeroSection] at h
    simpa [P0, b0] using h

  by_cases hzero : E.endpoint (0 : Fin 4) = 0
  · have hex : ∃ i : Fin 4, E.endpoint i ≠ 0 := by
      by_contra hnot
      push_neg at hnot
      apply E.endpoint_ne_zero
      funext i
      exact hnot i
    rcases hex with ⟨i, hi⟩
    have hi0 : (0 : Fin 4) ≠ i := by
      intro h
      subst i
      exact hi hzero
    let c : Polynomial K := Polynomial.C (-(E.endpoint i)⁻¹)
    let P1 := transverseSourceShearHom (K := K) (0 : Fin 4) i c P0
    let b1 := transverseSourceUnshearSection (0 : Fin 4) i c b0

    have hdef1 : HasPolynomialFamilyHessianDefect (K := K) P1 0 := by
      simpa [P1] using
        transverseSourceShearHom_preservesHessianDefect
          (K := K) (0 : Fin 4) i hi0 c P0 hdef0
    have hdegree1 : NonlinearDegreeBound E.degreeCap P1 := by
      simpa [P1] using
        nonlinearDegreeBound_transverseSourceShear
          E.degreeCap (0 : Fin 4) i c P0 hdegree0
    have hcoll1 :
        HasPolynomialFamilyExactGradientCollision
          P1 (zeroPolynomialSection (K := K)) b1 := by
      have h := polynomialFamilyExactGradientCollision_transverseSourceShear
        (K := K) (0 : Fin 4) i hi0 c P0
        (zeroPolynomialSection (K := K)) b0 hcoll0
      rw [transverseSourceUnshearSection_zero] at h
      simpa [P1, b1] using h
    have hb1zero :
        polynomialSectionSpecialPoint b1 (0 : Fin 4) = 1 := by
      have hinv : (E.endpoint i)⁻¹ * E.endpoint i = 1 :=
        inv_mul_cancel₀ hi
      simp [b1, b0, c, transverseSourceUnshearSection,
        polynomialSectionSpecialPoint, polynomialConstantSection, hzero]
      exact hinv
    exact ⟨{
      family := P1
      rightSection := b1
      hessianDefect := hdef1
      nonlinearDegreeBound := hdegree1
      exactCollision := hcoll1
      rightSpecialZero := hb1zero
    }⟩

  · let c1 : Polynomial K :=
      Polynomial.C ((E.endpoint (1 : Fin 4) - E.endpoint 0) / E.endpoint 0)
    let P1 := transverseSourceShearHom (K := K) (1 : Fin 4) (0 : Fin 4) c1 P0
    let b1 := transverseSourceUnshearSection (1 : Fin 4) (0 : Fin 4) c1 b0

    have hdef1 : HasPolynomialFamilyHessianDefect (K := K) P1 0 := by
      simpa [P1] using
        transverseSourceShearHom_preservesHessianDefect
          (K := K) (1 : Fin 4) (0 : Fin 4) (by decide) c1 P0 hdef0
    have hdegree1 : NonlinearDegreeBound E.degreeCap P1 := by
      simpa [P1] using
        nonlinearDegreeBound_transverseSourceShear
          E.degreeCap (1 : Fin 4) (0 : Fin 4) c1 P0 hdegree0
    have hcoll1 :
        HasPolynomialFamilyExactGradientCollision
          P1 (zeroPolynomialSection (K := K)) b1 := by
      have h := polynomialFamilyExactGradientCollision_transverseSourceShear
        (K := K) (1 : Fin 4) (0 : Fin 4) (by decide) c1 P0
        (zeroPolynomialSection (K := K)) b0 hcoll0
      rw [transverseSourceUnshearSection_zero] at h
      simpa [P1, b1] using h
    have hb1one :
        polynomialSectionSpecialPoint b1 (1 : Fin 4) = E.endpoint 0 := by
      simp [b1, b0, c1, transverseSourceUnshearSection,
        polynomialSectionSpecialPoint, polynomialConstantSection]
      field_simp [hzero]
      ring
    have hb1zero :
        polynomialSectionSpecialPoint b1 (0 : Fin 4) = E.endpoint 0 := by
      simp [b1, b0, c1, transverseSourceUnshearSection,
        polynomialSectionSpecialPoint, polynomialConstantSection]

    let c2 : Polynomial K :=
      Polynomial.C ((E.endpoint 0 - 1) / E.endpoint 0)
    let P2 := transverseSourceShearHom (K := K) (0 : Fin 4) (1 : Fin 4) c2 P1
    let b2 := transverseSourceUnshearSection (0 : Fin 4) (1 : Fin 4) c2 b1

    have hdef2 : HasPolynomialFamilyHessianDefect (K := K) P2 0 := by
      simpa [P2] using
        transverseSourceShearHom_preservesHessianDefect
          (K := K) (0 : Fin 4) (1 : Fin 4) (by decide) c2 P1 hdef1
    have hdegree2 : NonlinearDegreeBound E.degreeCap P2 := by
      simpa [P2] using
        nonlinearDegreeBound_transverseSourceShear
          E.degreeCap (0 : Fin 4) (1 : Fin 4) c2 P1 hdegree1
    have hcoll2 :
        HasPolynomialFamilyExactGradientCollision
          P2 (zeroPolynomialSection (K := K)) b2 := by
      have h := polynomialFamilyExactGradientCollision_transverseSourceShear
        (K := K) (0 : Fin 4) (1 : Fin 4) (by decide) c2 P1
        (zeroPolynomialSection (K := K)) b1 hcoll1
      rw [transverseSourceUnshearSection_zero] at h
      simpa [P2, b2] using h
    have hb2zero :
        polynomialSectionSpecialPoint b2 (0 : Fin 4) = 1 := by
      change Polynomial.constantCoeff (b1 0 - c2 * b1 1) = 1
      rw [map_sub, map_mul]
      change
        polynomialSectionSpecialPoint b1 0 -
          Polynomial.constantCoeff c2 * polynomialSectionSpecialPoint b1 1 = 1
      rw [hb1zero, hb1one]
      simp [c2]
      field_simp [hzero]
      ring
    exact ⟨{
      family := P2
      rightSection := b2
      hessianDefect := hdef2
      nonlinearDegreeBound := hdegree2
      exactCollision := hcoll2
      rightSpecialZero := hb2zero
    }⟩

/-- Determinant-one source transvections make the longitudinal coordinate one. -/
noncomputable def longitudinalOneData
    (E : AdaptiveAlignedSmithCanonicalPointedZeroDefectCollisionEntry (K := K)) :
    LongitudinalOneData E :=
  Classical.choice (longitudinalOneData_nonempty E)

/-- **A18.5.85 — pointed collision -> canonical axis collision.**

The output is exactly the non-vacuous zero-defect entry consumed by the
well-founded A18 rank-one termination trace. -/
noncomputable def toZeroDefectCollisionEntry
    (E : AdaptiveAlignedSmithCanonicalPointedZeroDefectCollisionEntry (K := K)) :
    AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K) := by
  let L := E.longitudinalOneData
  let N := pointedShearNormalisedFamily L.family L.rightSection
  let bN := pointedShearNormalisedSection L.rightSection
  let G := polynomialFamilySpecialFiber N

  have hdefN : HasPolynomialFamilyHessianDefect (K := K) N 0 := by
    simpa [N] using
      pointedShearNormalisedFamily_preservesHessianDefect
        (K := K) L.family L.rightSection L.hessianDefect
  have hdetG : HC4.Polynomial.hessianDeterminant G = 1 := by
    rw [show G = polynomialFamilySpecialFiber N by rfl]
    rw [hessianDeterminant_polynomialFamilySpecialFiber]
    unfold HasPolynomialFamilyHessianDefect at hdefN
    rw [hdefN]
    simp

  have hdegree1 : NonlinearDegreeBound E.degreeCap
      (pointedShearFamilyOne L.family L.rightSection) := by
    unfold pointedShearFamilyOne
    exact nonlinearDegreeBound_elementaryShear
      E.degreeCap (1 : Fin 4) (pointedShearCoeffOne L.rightSection)
      L.family L.nonlinearDegreeBound
  have hdegree2 : NonlinearDegreeBound E.degreeCap
      (pointedShearFamilyTwo L.family L.rightSection) := by
    unfold pointedShearFamilyTwo
    exact nonlinearDegreeBound_elementaryShear
      E.degreeCap (2 : Fin 4) (pointedShearCoeffTwo L.rightSection)
      (pointedShearFamilyOne L.family L.rightSection) hdegree1
  have hdegreeN : NonlinearDegreeBound E.degreeCap N := by
    unfold N pointedShearNormalisedFamily
    exact nonlinearDegreeBound_elementaryShear
      E.degreeCap (3 : Fin 4) (pointedShearCoeffThree L.rightSection)
      (pointedShearFamilyTwo L.family L.rightSection) hdegree2
  have hdegreeG : NonlinearDegreeBound E.degreeCap G := by
    simpa [G] using
      nonlinearDegreeBound_polynomialFamilySpecialFiber
        E.degreeCap N hdegreeN

  have hcollN :
      HasPolynomialFamilyExactGradientCollision
        N (zeroPolynomialSection (K := K)) bN := by
    simpa [N, bN] using
      pointedShearNormalisedFamily_preservesExactCollision
        (K := K) L.family L.rightSection L.exactCollision
  have hbN :
      polynomialSectionSpecialPoint bN =
        coordinateAxisPoint (K := K) (0 : Fin 4) := by
    simpa [bN] using
      pointedShearNormalisedSection_specialPoint
        (K := K) L.rightSection L.rightSpecialZero
  have hcollG :
      HasExactGradientCollision G
        (fun _ : Fin 4 => (0 : K))
        (coordinateAxisPoint (K := K) (0 : Fin 4)) := by
    have h := polynomialFamilyZeroCollision_specialFiber N bN hcollN
    rw [hbN] at h
    simpa [G] using h

  exact {
    degreeCap := E.degreeCap
    polynomial := G
    nonlinearDegreeBound := hdegreeG
    hessian_one := hdetG
    exactCollision := hcollG
  }

end AdaptiveAlignedSmithCanonicalPointedZeroDefectCollisionEntry

end

end HC4.Valuation
