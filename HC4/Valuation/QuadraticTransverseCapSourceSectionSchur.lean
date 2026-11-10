import HC4.Valuation.AdaptiveAlignedSmithRankOneQuadraticCompetitor
import HC4.Valuation.QuadraticTransverseCapAdjugateKernelNoPivot
import Mathlib.Tactic

/-!
# Exact source-to-Schur determinant bridge at transverse sections

This file works on the original four-variable polynomial, not a presented
or auxiliary source. The fixed-transverse-section homomorphism retains the
longitudinal variable and evaluates the other three coordinates at a
constant vector. Mapping the actual Hessian through this homomorphism
preserves its determinant.

The final axis specialization identifies the mixed Hessian entries with
derivatives of the ORIGINAL longitudinal coefficient polynomials.
No quadratic cap is needed for this determinant-transport lemma; the cap
will next identify the transverse block at all seven sections and the
affine transverse dependence of the mixed row.
-/

namespace HC4.Valuation

noncomputable section
open HC4.Newton

universe u
variable {K : Type u} [Field K]

/-- Restrict the genuine four-variable source to a fixed transverse
section while retaining its longitudinal variable as Polynomial.X. -/
noncomputable def quadraticSourceSectionRingHom (y : Fin 3 → K) :
    MvPolynomial (Fin 4) K →+* Polynomial K :=
  (Polynomial.mapRingHom (MvPolynomial.eval y)).comp
    (MvPolynomial.finSuccEquiv K 3).toRingEquiv.toRingHom

/-- The actual Hessian restricted to a fixed transverse section. -/
noncomputable def quadraticSourceSectionHessian
    (F : MvPolynomial (Fin 4) K) (y : Fin 3 → K) :
    Matrix (Fin 4) (Fin 4) (Polynomial K) :=
  (HC4.Polynomial.hessian F).map (quadraticSourceSectionRingHom y)

/-- The restricted Hessian is symmetric, by commutation of actual formal
mixed partial derivatives. -/
theorem quadraticSourceSectionHessian_symmetric
    (F : MvPolynomial (Fin 4) K) (y : Fin 3 → K)
    (i j : Fin 4) :
    quadraticSourceSectionHessian F y i j =
      quadraticSourceSectionHessian F y j i := by
  change
    quadraticSourceSectionRingHom y
        (MvPolynomial.pderiv j (MvPolynomial.pderiv i F)) =
      quadraticSourceSectionRingHom y
        (MvPolynomial.pderiv i (MvPolynomial.pderiv j F))
  congr 1
  exact (pderiv_comm_commRing i j F).symm

/-- Determinant-one for the actual Hessian implies the explicit symmetric
1+3 Schur core is identically one as a polynomial in the marked variable,
at EVERY constant transverse section. This is not a pointwise scalar
specialization. -/
theorem quadraticSourceSectionHessian_schurCore_one
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (y : Fin 3 → K) :
    let H := quadraticSourceSectionHessian F y
    quadraticAxisFourBlockCore
        (H 0 0) (H 0 1) (H 0 2) (H 0 3)
        (H 1 1) (H 1 2) (H 1 3)
        (H 2 2) (H 2 3) (H 3 3) = 1 := by
  dsimp only
  let f := quadraticSourceSectionRingHom y
  let H := quadraticSourceSectionHessian F y
  let B := GeneralFourBlock.ofSymmetricMatrix H
  have hsymm : ∀ i j : Fin 4, H i j = H j i := by
    intro i j
    exact quadraticSourceSectionHessian_symmetric F y i j
  have hdisplay : B.matrix = H :=
    GeneralFourBlock.matrix_ofSymmetricMatrix H hsymm
  have hdetH : H.det = (1 : Polynomial K) := by
    calc
      H.det = f (HC4.Polynomial.hessianDeterminant F) := by
        dsimp [H, quadraticSourceSectionHessian,
          f, HC4.Polynomial.hessianDeterminant]
        exact (RingHom.map_det
          (quadraticSourceSectionRingHom y)
          (HC4.Polynomial.hessian F)).symm
      _ = 1 := by rw [hdet]; simp
  have hcore :
      quadraticAxisFourBlockCore
          (H 0 0) (H 0 1) (H 0 2) (H 0 3)
          (H 1 1) (H 1 2) (H 1 3)
          (H 2 2) (H 2 3) (H 3 3) =
        B.determinantCore := by
    dsimp [B, GeneralFourBlock.ofSymmetricMatrix,
      quadraticAxisFourBlockCore, GeneralFourBlock.determinantCore]
    ring
  calc
    quadraticAxisFourBlockCore
        (H 0 0) (H 0 1) (H 0 2) (H 0 3)
        (H 1 1) (H 1 2) (H 1 3)
        (H 2 2) (H 2 3) (H 3 3) =
      B.determinantCore := hcore
    _ = B.matrix.det := (GeneralFourBlock.matrix_det B).symm
    _ = H.det := by rw [hdisplay]
    _ = 1 := hdetH

/-- The axis section is literally the existing source longitudinal
restriction ring hom, with no further coordinate change. -/
theorem quadraticSourceSectionRingHom_zero :
    quadraticSourceSectionRingHom (K := K) (fun _ : Fin 3 => 0) =
      longitudinalAxisRestrictionRingHom (K := K) := rfl

/-- On the genuine source axis, a mixed Hessian entry is exactly the
derivative of its genuine transverse-linear longitudinal coefficient. -/
theorem quadraticSourceSectionHessian_axis_mixed
    (F : MvPolynomial (Fin 4) K)
    (j : Fin 3) :
    quadraticSourceSectionHessian F (fun _ : Fin 3 => 0)
        0 j.succ =
      (longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F).derivative := by
  change
    longitudinalAxisRestriction
      (HC4.Polynomial.hessian F (0 : Fin 4) j.succ) =
      (longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F).derivative
  exact longitudinalAxisRestriction_hessian_zero_succ j F

/-- Actual transverse three-block on the marked axis. -/
noncomputable def quadraticSourceAxisThreeBlock
    (F : MvPolynomial (Fin 4) K) :
    GeneralThreeBlock (Polynomial K) where
  a := quadraticSourceSectionHessian F (fun _ => 0) 1 1
  b := quadraticSourceSectionHessian F (fun _ => 0) 1 2
  c := quadraticSourceSectionHessian F (fun _ => 0) 1 3
  d := quadraticSourceSectionHessian F (fun _ => 0) 2 2
  e := quadraticSourceSectionHessian F (fun _ => 0) 2 3
  f := quadraticSourceSectionHessian F (fun _ => 0) 3 3

/-- The *actual source* satisfies the longitudinal-axis determinant-one
Schur equation with the true derivative coefficient polynomials. -/
theorem quadraticSource_axisSchurCore_one
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    quadraticAxisFourBlockCore
      (quadraticSourceSectionHessian F (fun _ => 0) 0 0)
      ((longitudinalCoefficientPolynomialAt (Finsupp.single (0 : Fin 3) 1) F).derivative)
      ((longitudinalCoefficientPolynomialAt (Finsupp.single (1 : Fin 3) 1) F).derivative)
      ((longitudinalCoefficientPolynomialAt (Finsupp.single (2 : Fin 3) 1) F).derivative)
      (quadraticSourceAxisThreeBlock F).a
      (quadraticSourceAxisThreeBlock F).b
      (quadraticSourceAxisThreeBlock F).c
      (quadraticSourceAxisThreeBlock F).d
      (quadraticSourceAxisThreeBlock F).e
      (quadraticSourceAxisThreeBlock F).f = 1 := by
  change quadraticAxisFourBlockCore
      (quadraticSourceSectionHessian F (fun _ => 0) 0 0)
      ((longitudinalCoefficientPolynomialAt (Finsupp.single (0 : Fin 3) 1) F).derivative)
      ((longitudinalCoefficientPolynomialAt (Finsupp.single (1 : Fin 3) 1) F).derivative)
      ((longitudinalCoefficientPolynomialAt (Finsupp.single (2 : Fin 3) 1) F).derivative)
      (quadraticSourceSectionHessian F (fun _ => 0) 1 1)
      (quadraticSourceSectionHessian F (fun _ => 0) 1 2)
      (quadraticSourceSectionHessian F (fun _ => 0) 1 3)
      (quadraticSourceSectionHessian F (fun _ => 0) 2 2)
      (quadraticSourceSectionHessian F (fun _ => 0) 2 3)
      (quadraticSourceSectionHessian F (fun _ => 0) 3 3) = 1
  rw [← quadraticSourceSectionHessian_axis_mixed F (0 : Fin 3),
      ← quadraticSourceSectionHessian_axis_mixed F (1 : Fin 3),
      ← quadraticSourceSectionHessian_axis_mixed F (2 : Fin 3)]
  exact quadraticSourceSectionHessian_schurCore_one F hdet
    (fun _ : Fin 3 => 0)

end
end HC4.Valuation
