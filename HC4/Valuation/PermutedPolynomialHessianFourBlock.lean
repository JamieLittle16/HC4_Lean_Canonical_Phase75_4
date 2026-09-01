import HC4.Valuation.PermutedFamilyHessianFourBlock
import HC4.Polynomial.RankThreeDegreeOneEulerActiveMinor
import Mathlib.Tactic

/-!
# A19.R11: coordinate-permuted four-block of an ordinary polynomial Hessian

`PermutedFamilyHessianFourBlock` handles parameter families.  The A19.117
first strict superface is already an ordinary four-variable polynomial, so the
local Schur reduction should not wrap it in a fake constant family.

This file gives the state-free ordinary analogue.  Simultaneous source
permutation preserves the genuine Hessian determinant, and the active block
determinant is exactly the corresponding ordinary Hessian principal minor.
Thus a singular polynomial with a nonzero principal pivot immediately has a
zero denominator-cleared binary Schur determinant.

A19.R17 also records the exact Euler-scaled version needed by the final contact
adapter.  After the same coordinate permutation, the Euler-scaled Hessian
four-block is literally the ordinary block under the generic diagonal
congruence of `GeneralFourBlockSchur`, with the four source variables as the
row/column scales.  This keeps all subsequent Schur covariance algebra in the
single state-free R16 interface.

R20 deliberately states this layer over a commutative ring.  The final binary
contact family has coefficient ring `Polynomial K`, and none of the finite
Hessian, permutation, or Euler-congruence identities here uses division.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix

universe u
variable {K : Type u} [CommRing K]

/-- Ordinary polynomial Hessian is symmetric. -/
theorem polynomialHessian_symmetric
    (F : MvPolynomial (Fin 4) K) (i j : Fin 4) :
    HC4.Polynomial.hessian F i j = HC4.Polynomial.hessian F j i := by
  change MvPolynomial.pderiv j (MvPolynomial.pderiv i F) =
    MvPolynomial.pderiv i (MvPolynomial.pderiv j F)
  rw [pderiv_comm_commRing]

/-- Honest coordinate-permuted four-block of an ordinary polynomial Hessian. -/
noncomputable def permutedPolynomialHessianFourBlock
    (rho : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K) :
    GeneralFourBlock (MvPolynomial (Fin 4) K) :=
  GeneralFourBlock.ofSymmetricMatrix
    ((HC4.Polynomial.hessian F).submatrix rho rho)

/-- Displaying the block recovers the simultaneously permuted genuine Hessian. -/
theorem permutedPolynomialHessianFourBlock_matrix
    (rho : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K) :
    (permutedPolynomialHessianFourBlock rho F).matrix =
      (HC4.Polynomial.hessian F).submatrix rho rho := by
  apply GeneralFourBlock.matrix_ofSymmetricMatrix
  intro i j
  exact polynomialHessian_symmetric F (rho i) (rho j)

/-- The active determinant is exactly the ordinary Hessian principal minor on
the first two permuted coordinates. -/
theorem permutedPolynomialHessianFourBlock_activeDet
    (rho : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K) :
    (permutedPolynomialHessianFourBlock rho F).activeDet =
      HC4.Polynomial.hessianPrincipalMinor F (rho 0) (rho 1) := by
  unfold permutedPolynomialHessianFourBlock GeneralFourBlock.activeDet
    GeneralFourBlock.ofSymmetricMatrix HC4.Polynomial.hessianPrincipalMinor
  simp only [Matrix.submatrix_apply]
  rw [polynomialHessian_symmetric F (rho 1) (rho 0)]

/-- Simultaneous source-coordinate permutation preserves the ordinary Hessian
determinant exactly. -/
theorem permutedPolynomialHessianFourBlock_determinantCore
    (rho : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K) :
    (permutedPolynomialHessianFourBlock rho F).determinantCore =
      HC4.Polynomial.hessianDeterminant F := by
  calc
    (permutedPolynomialHessianFourBlock rho F).determinantCore =
        (permutedPolynomialHessianFourBlock rho F).matrix.det :=
      (GeneralFourBlock.matrix_det
        (permutedPolynomialHessianFourBlock rho F)).symm
    _ = ((HC4.Polynomial.hessian F).submatrix rho rho).det := by
      rw [permutedPolynomialHessianFourBlock_matrix]
    _ = (HC4.Polynomial.hessian F).det := by
      rw [Matrix.det_submatrix_equiv_self]
    _ = HC4.Polynomial.hessianDeterminant F := rfl

/-- A singular ordinary source polynomial has zero cleared binary Schur
determinant in every simultaneous coordinate permutation. -/
theorem permutedPolynomialHessianFourBlock_schurDetCore_eq_zero
    (rho : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 0) :
    (permutedPolynomialHessianFourBlock rho F).schurDetCore = 0 := by
  apply GeneralFourBlock.schurDetCore_eq_zero_of_determinantCore_eq_zero
  rw [permutedPolynomialHessianFourBlock_determinantCore, hdet]

/-- **A19.R17/R20 Euler/four-block covariance.**

After simultaneous coordinate permutation, the Euler-scaled Hessian is exactly
the ordinary Hessian four-block under diagonal congruence by the four source
coordinate monomials.  In particular all denominator-cleared Schur covariance
can now be discharged by the generic R16 `diagonalScale` identities. -/
theorem permutedEulerScaledHessianFourBlock_eq_diagonalScale
    (rho : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K) :
    GeneralFourBlock.ofSymmetricMatrix
        ((HC4.Polynomial.eulerScaledHessian F).submatrix rho rho) =
      (permutedPolynomialHessianFourBlock rho F).diagonalScale
        (MvPolynomial.X (rho 0)) (MvPolynomial.X (rho 1))
        (MvPolynomial.X (rho 2)) (MvPolynomial.X (rho 3)) := by
  have hentry (i j : Fin 4) :
      HC4.Polynomial.eulerScaledHessian F i j =
        MvPolynomial.X i * MvPolynomial.X j *
          HC4.Polynomial.hessian F i j := by
    rw [HC4.Polynomial.eulerScaledHessian_apply,
      HC4.Polynomial.hessian_apply]
    rw [pderiv_comm_commRing]
  ext <;>
    simp [GeneralFourBlock.ofSymmetricMatrix,
      GeneralFourBlock.diagonalScale,
      permutedPolynomialHessianFourBlock,
      Matrix.submatrix_apply, hentry]

end

end HC4.Valuation
