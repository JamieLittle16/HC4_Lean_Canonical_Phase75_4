import HC4.Valuation.SmithFrontierFourBlockExtraction
import Mathlib.Tactic

/-!
# Generic coordinate-permuted Hessian four-block for polynomial families

`familyHessianFourBlock` fixes source coordinates `(0,1 | 2,3)`.  Several late
local arguments, including the lower-`.qs` contact staircase, know a more
natural active pair.  The scale-aware state stack already has a permutation-
aware four-block, but an auxiliary polynomial family should not be wrapped in a
fake global state merely to reuse it.

This file is the state-free analogue: simultaneously permute rows and columns
of the genuine parameter-first Hessian and package the result as the existing
`GeneralFourBlock`.  Determinant invariance under a simultaneous permutation
retains the exact pure Hessian clock.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open scoped Matrix

variable {K : Type*} [Field K]

/-- Honest coordinate-permuted Hessian four-block of an arbitrary polynomial
family. -/
noncomputable def permutedFamilyHessianFourBlock
    (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    GeneralFourBlock (Polynomial (MvPolynomial (Fin 4) K)) :=
  GeneralFourBlock.ofSymmetricMatrix
    ((parameterFirstHessian P).submatrix rho rho)

/-- Displayed matrix is literally the simultaneously permuted genuine Hessian
series. -/
theorem permutedFamilyHessianFourBlock_matrix
    (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (permutedFamilyHessianFourBlock rho P).matrix =
      (parameterFirstHessian P).submatrix rho rho := by
  apply GeneralFourBlock.matrix_ofSymmetricMatrix
  intro i j
  exact parameterFirstHessian_symmetric P (rho i) (rho j)

/-- Simultaneous source-coordinate permutation preserves the exact family
Hessian determinant clock. -/
theorem permutedFamilyHessianFourBlock_determinantCore_eq_X_pow
    (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K))
    {Delta : ℕ}
    (hdef : HasPolynomialFamilyHessianDefect (K := K) P Delta) :
    (permutedFamilyHessianFourBlock rho P).determinantCore =
      (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^ Delta := by
  calc
    (permutedFamilyHessianFourBlock rho P).determinantCore =
        (permutedFamilyHessianFourBlock rho P).matrix.det :=
      (GeneralFourBlock.matrix_det
        (permutedFamilyHessianFourBlock rho P)).symm
    _ = ((parameterFirstHessian P).submatrix rho rho).det := by
      rw [permutedFamilyHessianFourBlock_matrix]
    _ = (parameterFirstHessian P).det := by
      rw [Matrix.det_submatrix_equiv_self]
    _ = (Polynomial.X : Polynomial (MvPolynomial (Fin 4) K)) ^ Delta :=
      parameterFirstHessian_det_eq_X_pow P hdef

end

end HC4.Valuation
