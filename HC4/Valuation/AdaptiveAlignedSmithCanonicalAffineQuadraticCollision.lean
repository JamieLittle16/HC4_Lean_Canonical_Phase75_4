import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroDefectSingularTopFace
import HC4.Valuation.QuadraticFamilyCollision
import HC4.Newton.MixedDegreeWallRefinement
import Mathlib.Tactic

/-!
# A18.5.11: determinant-one affine quadratics cannot carry a collision

The zero-defect terminal special fibre has Hessian determinant one.  To show
that its attained maximal ordinary degree is genuinely nonlinear, we must
exclude not only homogeneous quadratics but arbitrary polynomials of ordinary
degree at most two.

The exact quadratic initial component is enough.  For ordinary weight one:

* the first derivative of the discarded lower part has weight `< 1`, hence is
  constant;
* therefore every exact gradient collision descends to the quadratic initial
  component;
* the maximal-Hessian identity shows that the quadratic initial component
  still has Hessian determinant one.

The existing domain-level quadratic injectivity theorem then identifies the
two collision points.  No global homogeneity assumption is used.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial
open HC4.Newton

universe u
variable {K : Type u} [Field K] [CharZero K]

private def ordinaryWeight : Fin 4 → ℤ := fun _ => 1

/-- A polynomial strictly below ordinary degree one is constant. -/
theorem ordinaryWeightLT_one_eq_C_constantCoeff
    (P : MvPolynomial (Fin 4) K)
    (hP : HC4.Polynomial.IsWeightLT ordinaryWeight 1 P) :
    P = MvPolynomial.C (MvPolynomial.constantCoeff P) := by
  apply homogeneous_zero_eq_C_constantCoeff_domain
  intro d hd
  have hlt := hP (MvPolynomial.mem_support_iff.mpr hd)
  change Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) d < 1 at hlt
  rw [HC4.Newton.ordinaryIntegerWeight_eq_ordinaryDegree4] at hlt
  have hdeg4 : HC4.Polynomial.ordinaryDegree4 d = 0 := by
    omega
  have hw : Finsupp.weight (1 : Fin 4 → ℕ) d = d.degree :=
    (congrFun Finsupp.degree_eq_weight_one d).symm
  exact hw.trans ((finsuppDegree_eq_ordinaryDegree4 d).trans hdeg4)

/-- The exact ordinary degree-two component is genuinely homogeneous of
ordinary degree two. -/
theorem ordinaryQuadraticInitial_isHomogeneous_two
    (F : MvPolynomial (Fin 4) K) :
    (HC4.Polynomial.initialForm ordinaryWeight 2 F).IsHomogeneous 2 := by
  intro d hd
  have hhom :=
    HC4.Polynomial.initialForm_isWeightedHomogeneous
      ordinaryWeight (2 : ℤ) F
  have hz := hhom hd
  change Finsupp.weight (fun _ : Fin 4 => (1 : ℤ)) d = 2 at hz
  rw [HC4.Newton.ordinaryIntegerWeight_eq_ordinaryDegree4] at hz
  have hdeg4 : HC4.Polynomial.ordinaryDegree4 d = 2 := by
    exact_mod_cast hz
  have hw : Finsupp.weight (1 : Fin 4 → ℕ) d = d.degree :=
    (congrFun Finsupp.degree_eq_weight_one d).symm
  exact hw.trans ((finsuppDegree_eq_ordinaryDegree4 d).trans hdeg4)

/-- An exact collision of a degree-at-most-two polynomial descends to its
quadratic initial component.  The discarded affine part contributes only a
constant to each gradient component. -/
theorem exactGradientCollision_ordinaryQuadraticInitial
    (F : MvPolynomial (Fin 4) K)
    (a b : Fin 4 → K)
    (hLE : HC4.Polynomial.IsWeightLE ordinaryWeight 2 F)
    (hcoll : HasExactGradientCollision F a b) :
    HasExactGradientCollision
      (HC4.Polynomial.initialForm ordinaryWeight 2 F) a b := by
  intro i
  unfold mvGradientComponentAt
  let Q := HC4.Polynomial.initialForm ordinaryWeight 2 F
  have hderiv :
      MvPolynomial.pderiv i Q =
        HC4.Polynomial.initialForm ordinaryWeight 1
          (MvPolynomial.pderiv i F) := by
    dsimp [Q]
    simpa [ordinaryWeight] using
      (HC4.Polynomial.pderiv_initialForm
        ordinaryWeight (2 : ℤ) F i)
  have hPiLE :
      HC4.Polynomial.IsWeightLE ordinaryWeight 1
        (MvPolynomial.pderiv i F) := by
    have h := hLE.pderiv i
    simpa [ordinaryWeight] using h
  let R := MvPolynomial.pderiv i F - MvPolynomial.pderiv i Q
  have hRlt : HC4.Polynomial.IsWeightLT ordinaryWeight 1 R := by
    dsimp [R]
    rw [hderiv]
    exact HC4.Polynomial.sub_initialForm_isWeightLT hPiLE
  have hRconst := ordinaryWeightLT_one_eq_C_constantCoeff R hRlt
  have hReval : MvPolynomial.eval a R = MvPolynomial.eval b R := by
    rw [hRconst]
    simp
  have hFi := hcoll i
  unfold mvGradientComponentAt at hFi
  have hdecomp :
      MvPolynomial.pderiv i F = R + MvPolynomial.pderiv i Q := by
    dsimp [R]
    ring
  calc
    MvPolynomial.eval a (MvPolynomial.pderiv i Q) =
        MvPolynomial.eval a (MvPolynomial.pderiv i F) -
          MvPolynomial.eval a R := by
      rw [hdecomp]
      simp
    _ = MvPolynomial.eval b (MvPolynomial.pderiv i F) -
          MvPolynomial.eval b R := by
      rw [hFi, hReval]
    _ = MvPolynomial.eval b (MvPolynomial.pderiv i Q) := by
      rw [hdecomp]
      simp

/-- If a polynomial of ordinary degree at most two has determinant-one
Hessian, then its exact quadratic component also has determinant-one Hessian. -/
theorem hessianDeterminant_ordinaryQuadraticInitial_eq_one
    (F : MvPolynomial (Fin 4) K)
    (hLE : HC4.Polynomial.IsWeightLE ordinaryWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    HC4.Polynomial.hessianDeterminant
      (HC4.Polynomial.initialForm ordinaryWeight 2 F) = 1 := by
  have htop :=
    HC4.Polynomial.initialForm_hessianDeterminant_eq_hessianDeterminant_initialForm
      ordinaryWeight (2 : ℤ) F hLE
  have hweight :
      (Fintype.card (Fin 4) : ℤ) * 2 -
          2 * ∑ i : Fin 4, ordinaryWeight i = 0 := by
    simp [ordinaryWeight]
  rw [hweight, hdet] at htop
  have hone :
      HC4.Polynomial.initialForm ordinaryWeight 0
          (1 : MvPolynomial (Fin 4) K) = 1 := by
    exact HC4.Polynomial.initialForm_eq_self_of_isWeightedHomogeneous
      (MvPolynomial.isWeightedHomogeneous_one K ordinaryWeight)
  rw [hone] at htop
  exact htop.symm

/-- **Affine-quadratic collision exclusion.**

A four-variable polynomial of ordinary degree at most two with Hessian
determinant one has injective gradient.  Hence it cannot carry a distinct
exact gradient collision. -/
theorem exactGradientCollision_impossible_of_ordinaryDegree_le_two
    (F : MvPolynomial (Fin 4) K)
    (a b : Fin 4 → K)
    (hLE : HC4.Polynomial.IsWeightLE ordinaryWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hab : a ≠ b)
    (hcoll : HasExactGradientCollision F a b) :
    False := by
  let Q := HC4.Polynomial.initialForm ordinaryWeight 2 F
  have hQhom : Q.IsHomogeneous 2 := by
    simpa [Q] using ordinaryQuadraticInitial_isHomogeneous_two F
  have hQcoll : HasExactGradientCollision Q a b := by
    simpa [Q] using exactGradientCollision_ordinaryQuadraticInitial
      F a b hLE hcoll
  have hQdet : HC4.Polynomial.hessianDeterminant Q = 1 := by
    simpa [Q] using
      hessianDeterminant_ordinaryQuadraticInitial_eq_one F hLE hdet
  have hmatrixDet : (quadraticFamilyHessianMatrix Q).det ≠ 0 := by
    rw [quadraticFamilyHessianMatrix_det, hQdet]
    simp
  have heq : a = b :=
    homogeneous_two_exactGradientCollision_eq_domain
      hQhom a b (by
        intro i
        simpa [mvGradientComponentAt] using hQcoll i)
      hmatrixDet
  exact hab heq

end

end HC4.Valuation
