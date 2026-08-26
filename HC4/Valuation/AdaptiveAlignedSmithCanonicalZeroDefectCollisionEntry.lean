import HC4.Valuation.AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
import HC4.Valuation.NonlinearDegreeBoundPreservation
import Mathlib.Tactic

/-!
# A18.5.76: valid zero-defect entry for a normalized Keller collision

The legacy `CanonicalExactCollisionEntry` is intentionally unusable for the
final HC4 theorem: it asks the *whole* source polynomial to be homogeneous,
which is incompatible with a nonzero constant Hessian determinant in degree
at least three.

The scale-aware A18 machine has no such hypothesis.  A normalized polynomial
with

* `det Hess F = 1`;
* a finite nonlinear source-degree cap; and
* an exact gradient collision `0 ~ e₀`

enters it directly as the constant parameter family.  Its raw Hessian clock is
`0`, its parameter scale is `1`, and its repair coordinate is the canonical
rank-one state expected by A18.4.109.

This is the non-vacuous global front door needed by the proposition-level HC4
assembly.  No JC2 hypothesis and no full-family homogeneity is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- Regard an ordinary four-variable polynomial as a family constant in the
A18 parameter. -/
noncomputable def zeroDefectConstantParameterFamily
    (F : MvPolynomial (Fin 4) K) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  MvPolynomial.map Polynomial.C F

/-- The special fibre of the constant family is literally the original
polynomial. -/
@[simp] theorem polynomialFamilySpecialFiber_zeroDefectConstantParameterFamily
    (F : MvPolynomial (Fin 4) K) :
    polynomialFamilySpecialFiber (zeroDefectConstantParameterFamily F) = F := by
  apply MvPolynomial.ext
  intro d
  unfold polynomialFamilySpecialFiber zeroDefectConstantParameterFamily
  rw [MvPolynomial.coeff_map, MvPolynomial.coeff_map]
  simp

/-- Source Hessians commute with the coefficient embedding `K -> K[tau]`. -/
theorem hessian_zeroDefectConstantParameterFamily
    (F : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.hessian (zeroDefectConstantParameterFamily F) =
      (MvPolynomial.map Polynomial.C).mapMatrix
        (HC4.Polynomial.hessian F) := by
  apply Matrix.ext
  intro i j
  simp [HC4.Polynomial.hessian_apply,
    zeroDefectConstantParameterFamily, MvPolynomial.pderiv_map]

/-- Consequently the Hessian determinant of the constant family is the
coefficient embedding of the ordinary Hessian determinant. -/
theorem hessianDeterminant_zeroDefectConstantParameterFamily
    (F : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.hessianDeterminant
        (zeroDefectConstantParameterFamily F) =
      MvPolynomial.map Polynomial.C
        (HC4.Polynomial.hessianDeterminant F) := by
  unfold HC4.Polynomial.hessianDeterminant
  rw [hessian_zeroDefectConstantParameterFamily]
  let f : MvPolynomial (Fin 4) K →+*
      MvPolynomial (Fin 4) (Polynomial K) :=
    MvPolynomial.map Polynomial.C
  exact (RingHom.map_det f (HC4.Polynomial.hessian F)).symm

/-- Determinant one is exactly raw A18 defect zero for the constant family. -/
theorem zeroDefectConstantParameterFamily_hessianDefect
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    HasPolynomialFamilyHessianDefect
      (K := K) (zeroDefectConstantParameterFamily F) 0 := by
  unfold HasPolynomialFamilyHessianDefect
  rw [hessianDeterminant_zeroDefectConstantParameterFamily, hdet]
  simp

/-- Constant coefficient embedding preserves an exact ordinary gradient
collision as an exact polynomial-family collision between constant sections. -/
theorem zeroDefectConstantParameterFamily_exactCollision
    (F : MvPolynomial (Fin 4) K)
    (p q : Fin 4 → K)
    (hcoll : HasExactGradientCollision F p q) :
    HasPolynomialFamilyExactGradientCollision
      (zeroDefectConstantParameterFamily F)
      (polynomialConstantSection p)
      (polynomialConstantSection q) := by
  intro i
  have hi := hcoll i
  unfold zeroDefectConstantParameterFamily
  rw [MvPolynomial.pderiv_map]
  rw [MvPolynomial.eval_map, MvPolynomial.eval_map]
  have hp :
      Polynomial.C
          (MvPolynomial.eval p (MvPolynomial.pderiv i F)) =
        MvPolynomial.eval₂ Polynomial.C
          (polynomialConstantSection p) (MvPolynomial.pderiv i F) := by
    simpa [polynomialConstantSection] using
      (MvPolynomial.eval₂_comp Polynomial.C p (MvPolynomial.pderiv i F))
  have hq :
      Polynomial.C
          (MvPolynomial.eval q (MvPolynomial.pderiv i F)) =
        MvPolynomial.eval₂ Polynomial.C
          (polynomialConstantSection q) (MvPolynomial.pderiv i F) := by
    simpa [polynomialConstantSection] using
      (MvPolynomial.eval₂_comp Polynomial.C q (MvPolynomial.pderiv i F))
  calc
    MvPolynomial.eval₂ Polynomial.C
        (polynomialConstantSection p) (MvPolynomial.pderiv i F) =
      Polynomial.C (MvPolynomial.eval p (MvPolynomial.pderiv i F)) := hp.symm
    _ = Polynomial.C (MvPolynomial.eval q (MvPolynomial.pderiv i F)) :=
      congrArg Polynomial.C hi
    _ = MvPolynomial.eval₂ Polynomial.C
        (polynomialConstantSection q) (MvPolynomial.pderiv i F) := hq

/-- Constant coefficient embedding cannot introduce new source monomials, so
it preserves every nonlinear degree cap. -/
theorem zeroDefectConstantParameterFamily_nonlinearDegreeBound
    (F : MvPolynomial (Fin 4) K)
    (degreeCap : ℕ)
    (hdegree : NonlinearDegreeBound degreeCap F) :
    NonlinearDegreeBound degreeCap (zeroDefectConstantParameterFamily F) := by
  exact nonlinearDegreeBound_of_support_subset hdegree
    (MvPolynomial.support_map_subset Polynomial.C F)

/-- Exact normalized data required to enter the unconditional A18 collision
machine.  This is deliberately a polynomial-level object, not another
homogeneous family wrapper. -/
structure AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry where
  degreeCap : ℕ
  polynomial : MvPolynomial (Fin 4) K
  nonlinearDegreeBound : NonlinearDegreeBound degreeCap polynomial
  hessian_one : HC4.Polynomial.hessianDeterminant polynomial = 1
  exactCollision :
    HasExactGradientCollision polynomial
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4))

namespace AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry

/-- The valid normalized entry as a literal scale-aware A18 state. -/
noncomputable def toScaleAwareState
    (E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K))
    (complexity : ℕ) :
    ScaleAwareAdaptiveGeometricRestartState (K := K) where
  rawDefect := 0
  scale := 1
  scale_pos := by omega
  degreeCap := E.degreeCap
  sourceComplexity := 0
  repair := rankOneRepairState complexity
  family := zeroDefectConstantParameterFamily E.polynomial
  movingSection :=
    polynomialConstantSection
      (coordinateAxisPoint (K := K) (0 : Fin 4))
  hessianDefect :=
    zeroDefectConstantParameterFamily_hessianDefect
      E.polynomial E.hessian_one
  nonlinearDegreeBound :=
    zeroDefectConstantParameterFamily_nonlinearDegreeBound
      E.polynomial E.degreeCap E.nonlinearDegreeBound
  exactCollision := by
    have h := zeroDefectConstantParameterFamily_exactCollision
      E.polynomial
      (fun _ : Fin 4 => (0 : K))
      (coordinateAxisPoint (K := K) (0 : Fin 4))
      E.exactCollision
    have hzeroSection :
        polynomialConstantSection (fun _ : Fin 4 => (0 : K)) =
          zeroPolynomialSection (K := K) := by
      funext i
      simp [polynomialConstantSection, zeroPolynomialSection]
    rw [hzeroSection] at h
    exact h
  sectionSpecial := by
    exact polynomialSectionSpecialPoint_constantSection
      (coordinateAxisPoint (K := K) (0 : Fin 4))

@[simp] theorem toScaleAwareState_rawDefect
    (E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K))
    (complexity : ℕ) :
    (E.toScaleAwareState complexity).rawDefect = 0 := rfl

@[simp] theorem toScaleAwareState_scale
    (E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K))
    (complexity : ℕ) :
    (E.toScaleAwareState complexity).scale = 1 := rfl

@[simp] theorem toScaleAwareState_repair
    (E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K))
    (complexity : ℕ) :
    (E.toScaleAwareState complexity).repair =
      rankOneRepairState complexity := rfl

@[simp] theorem toScaleAwareState_specialFiber
    (E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K))
    (complexity : ℕ) :
    polynomialFamilySpecialFiber (E.toScaleAwareState complexity).family =
      E.polynomial := by
  simp [toScaleAwareState]

/-- **A18.5.76 entry-to-termination theorem.**
Every normalized determinant-one exact collision enters A18.4.109 directly
and therefore has a finite certified rank-one termination trace ending in the
complete rank-three terminal geometry. -/
noncomputable def rankOneTerminationTrace
    (RR : RepairRanking)
    (E : AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry (K := K))
    (complexity : ℕ) :
    AdaptiveAlignedSmithCanonicalRankOneTerminationTrace
      RR complexity (E.toScaleAwareState complexity) :=
  (E.toScaleAwareState complexity).rankOneTerminationTrace
    RR complexity rfl

end AdaptiveAlignedSmithCanonicalZeroDefectCollisionEntry

end

end HC4.Valuation