import HC4.Valuation.QuadraticTransverseCapSourceSupport
import HC4.Valuation.AdaptiveAlignedSmithRankOneQuadraticCompetitor
import HC4.Valuation.QuadraticTransverseCapRankTwoOppositeSections
import Mathlib.Tactic

/-!
# Actual represented-source Hessian determinant on the marked axis

This module transports the determinant-one identity for an actual
four-variable potential F through the already existing bundled
longitudinal-axis restriction ring homomorphism. No transverse rank or
quadratic-cap assumption is needed to obtain the axis Schur equation.

Unlike a bare polynomial four-block assumed to have unit determinant,
the resulting block comes directly from HC4.Polynomial.hessian F.
This supplies the first of the five exact Schur equations needed by
the rank-two opposite-section endpoint.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K]

/-- The actual Hessian restricted coefficientwise to the longitudinal
source axis, packaged using the existing symmetric four-block API. -/
noncomputable def quadraticTransverseCapSourceAxisFourBlock
    (F : MvPolynomial (Fin 4) K) : GeneralFourBlock (Polynomial K) :=
  GeneralFourBlock.ofSymmetricMatrix
    ((HC4.Polynomial.hessian F).map
      (longitudinalAxisRestrictionRingHom (K := K)))

/-- The source Hessian is symmetric after applying axis restriction.
This equality is independent of the transverse quadratic cap. -/
theorem quadraticTransverseCapSourceAxisHessian_symmetric
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 4) :
    ((HC4.Polynomial.hessian F).map
      (longitudinalAxisRestrictionRingHom (K := K))) i j =
    ((HC4.Polynomial.hessian F).map
      (longitudinalAxisRestrictionRingHom (K := K))) j i := by
  change
    longitudinalAxisRestrictionRingHom (K := K)
        (MvPolynomial.pderiv j (MvPolynomial.pderiv i F)) =
      longitudinalAxisRestrictionRingHom (K := K)
        (MvPolynomial.pderiv i (MvPolynomial.pderiv j F))
  congr 1
  exact (pderiv_comm_commRing i j F).symm

/-- The complete actual four-block retains determinant one after
restriction to the marked axis. No invented family or determinant
assumption on a graded special fibre is introduced. -/
theorem quadraticTransverseCapSourceAxisFourBlock_unit
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    (quadraticTransverseCapSourceAxisFourBlock F).determinantCore = 1 := by
  let phi : MvPolynomial (Fin 4) K →+* Polynomial K :=
    longitudinalAxisRestrictionRingHom (K := K)
  let H : Matrix (Fin 4) (Fin 4) (Polynomial K) :=
    (HC4.Polynomial.hessian F).map phi
  have hsymm : ∀ i j : Fin 4, H i j = H j i := by
    intro i j
    exact quadraticTransverseCapSourceAxisHessian_symmetric F i j
  have hmat :
      (quadraticTransverseCapSourceAxisFourBlock F).matrix = H :=
    GeneralFourBlock.matrix_ofSymmetricMatrix H hsymm
  calc
    (quadraticTransverseCapSourceAxisFourBlock F).determinantCore =
        (quadraticTransverseCapSourceAxisFourBlock F).matrix.det :=
      (GeneralFourBlock.matrix_det _).symm
    _ = H.det := by rw [hmat]
    _ = phi ((HC4.Polynomial.hessian F).det) := by
      exact (phi.map_det (HC4.Polynomial.hessian F)).symm
    _ = phi (HC4.Polynomial.hessianDeterminant F) := rfl
    _ = 1 := by rw [hdet]; simp

/-- Pure algebra connecting the stored general four-block determinant to
the scalar-plus-transverse three-block Schur determinant. -/
theorem quadraticAxisFourBlockCore_eq_generalFourBlock
    {R : Type*} [CommRing R]
    (H : GeneralFourBlock R) :
    quadraticAxisFourBlockCore H.a H.b H.p H.q
      H.d H.r H.s H.x H.y H.z = H.determinantCore := by
  unfold quadraticAxisFourBlockCore GeneralFourBlock.determinantCore
  ring

/-- The real three-by-three transverse Hessian block of the original
source, evaluated on the marked longitudinal axis. -/
noncomputable def quadraticTransverseCapSourceAxisThreeBlock
    (F : MvPolynomial (Fin 4) K) : GeneralThreeBlock (Polynomial K) :=
  let H := quadraticTransverseCapSourceAxisFourBlock F
  { a := H.d
    b := H.r
    c := H.s
    d := H.x
    e := H.y
    f := H.z }

/-- Coefficients of the three transverse-linear source terms collected
as univariate polynomials in the actual longitudinal source variable. -/
noncomputable def quadraticTransverseCapSourceLinearCoefficients
    (F : MvPolynomial (Fin 4) K) : Fin 3 → Polynomial K :=
  fun j => longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F

/-- The actual axis Schur determinant, expressed in terms of the source's
own mixed longitudinal derivatives and three-by-three transverse block. -/
theorem quadraticTransverseCapSource_axisSchur_unit
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    let H := quadraticTransverseCapSourceAxisFourBlock F
    let C := quadraticTransverseCapSourceAxisThreeBlock F
    let b := quadraticTransverseCapSourceLinearCoefficients F
    quadraticAxisFourBlockCore H.a
      (Polynomial.derivative (b 0))
      (Polynomial.derivative (b 1))
      (Polynomial.derivative (b 2))
      C.a C.b C.c C.d C.e C.f = 1 := by
  dsimp only
  let H := quadraticTransverseCapSourceAxisFourBlock F
  let C := quadraticTransverseCapSourceAxisThreeBlock F
  let b := quadraticTransverseCapSourceLinearCoefficients F
  have hv0 : Polynomial.derivative (b 0) = H.b := by
    simpa [b, H, quadraticTransverseCapSourceLinearCoefficients,
      quadraticTransverseCapSourceAxisFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (longitudinalAxisRestriction_hessian_zero_succ (0 : Fin 3) F).symm
  have hv1 : Polynomial.derivative (b 1) = H.p := by
    simpa [b, H, quadraticTransverseCapSourceLinearCoefficients,
      quadraticTransverseCapSourceAxisFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (longitudinalAxisRestriction_hessian_zero_succ (1 : Fin 3) F).symm
  have hv2 : Polynomial.derivative (b 2) = H.q := by
    simpa [b, H, quadraticTransverseCapSourceLinearCoefficients,
      quadraticTransverseCapSourceAxisFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (longitudinalAxisRestriction_hessian_zero_succ (2 : Fin 3) F).symm
  rw [hv0, hv1, hv2]
  change quadraticAxisFourBlockCore H.a H.b H.p H.q
    H.d H.r H.s H.x H.y H.z = 1
  rw [quadraticAxisFourBlockCore_eq_generalFourBlock]
  exact quadraticTransverseCapSourceAxisFourBlock_unit F hdet

end

end HC4.Valuation
