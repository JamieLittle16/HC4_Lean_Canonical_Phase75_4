import HC4.Valuation.PermutedPolynomialHessianFourBlock
import HC4.Valuation.AdaptiveSmithWallExposure
import Mathlib.Tactic

/-!
# Source-first four-block covariance under adaptive diagonal inflation

The adaptive source inflation is an honest diagonal substitution.  Hessian
entries therefore transform by one source monomial on each differentiated
row/column.  Packaging those entries as a `GeneralFourBlock` turns this into
exact diagonal congruence, so the existing denominator-cleared Schur
covariance formulas apply without a fresh determinant expansion.

The same file records the two elementary coefficient-ring operations used by
the reverse-Rees normalization: embedding an ordinary source as a constant
family, and multiplying a family by a parameter scalar.  The cleared Schur
entries are cubic in Hessian entries, so the latter operation contributes the
third power of the scalar.

This file is state-free.  In particular it introduces no Schur clock and no
comparison between auxiliary and terminal defects.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

universe u
variable {K : Type u} [Field K]

/-- The ordinary source-first Hessian four-block of an adaptively inflated
family is the inflated original four-block under the corresponding diagonal
congruence. -/
theorem permutedPolynomialHessianFourBlock_adaptiveSmithInflateHom
    (W : Fin 4 → ℕ) (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    permutedPolynomialHessianFourBlock rho (adaptiveSmithInflateHom W P) =
      ((permutedPolynomialHessianFourBlock rho P).map
        (adaptiveSmithInflateHom (K := K) W)).diagonalScale
        (MvPolynomial.C (Polynomial.X ^ W (rho 0)))
        (MvPolynomial.C (Polynomial.X ^ W (rho 1)))
        (MvPolynomial.C (Polynomial.X ^ W (rho 2)))
        (MvPolynomial.C (Polynomial.X ^ W (rho 3))) := by
  ext <;>
    simp [permutedPolynomialHessianFourBlock,
      GeneralFourBlock.ofSymmetricMatrix,
      GeneralFourBlock.map, GeneralFourBlock.diagonalScale,
      Matrix.submatrix_apply,
      hessian_adaptiveSmithInflateHom_entry, mul_assoc]

/-- Cleared Schur `A` transforms by the exact cubic diagonal weight. -/
theorem schurA_adaptiveSmithInflateHom
    (W : Fin 4 → ℕ) (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (permutedPolynomialHessianFourBlock rho
        (adaptiveSmithInflateHom W P)).schurA =
      (MvPolynomial.C (Polynomial.X ^ W (rho 0)) *
        MvPolynomial.C (Polynomial.X ^ W (rho 1))) ^ 2 *
      (MvPolynomial.C (Polynomial.X ^ W (rho 2))) ^ 2 *
      adaptiveSmithInflateHom W
        (permutedPolynomialHessianFourBlock rho P).schurA := by
  have h := congrArg GeneralFourBlock.schurA
    (permutedPolynomialHessianFourBlock_adaptiveSmithInflateHom W rho P)
  simpa using h

/-- Cleared Schur `B` transforms by the exact cubic diagonal weight. -/
theorem schurB_adaptiveSmithInflateHom
    (W : Fin 4 → ℕ) (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (permutedPolynomialHessianFourBlock rho
        (adaptiveSmithInflateHom W P)).schurB =
      (MvPolynomial.C (Polynomial.X ^ W (rho 0)) *
        MvPolynomial.C (Polynomial.X ^ W (rho 1))) ^ 2 *
      MvPolynomial.C (Polynomial.X ^ W (rho 2)) *
      MvPolynomial.C (Polynomial.X ^ W (rho 3)) *
      adaptiveSmithInflateHom W
        (permutedPolynomialHessianFourBlock rho P).schurB := by
  have h := congrArg GeneralFourBlock.schurB
    (permutedPolynomialHessianFourBlock_adaptiveSmithInflateHom W rho P)
  simpa [mul_assoc] using h

/-- Cleared Schur `C` transforms by the exact cubic diagonal weight. -/
theorem schurC_adaptiveSmithInflateHom
    (W : Fin 4 → ℕ) (rho : Equiv.Perm (Fin 4))
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (permutedPolynomialHessianFourBlock rho
        (adaptiveSmithInflateHom W P)).schurC =
      (MvPolynomial.C (Polynomial.X ^ W (rho 0)) *
        MvPolynomial.C (Polynomial.X ^ W (rho 1))) ^ 2 *
      (MvPolynomial.C (Polynomial.X ^ W (rho 3))) ^ 2 *
      adaptiveSmithInflateHom W
        (permutedPolynomialHessianFourBlock rho P).schurC := by
  have h := congrArg GeneralFourBlock.schurC
    (permutedPolynomialHessianFourBlock_adaptiveSmithInflateHom W rho P)
  simpa using h

/-! ## Constant-family and scalar covariance -/

/-- Embedding an ordinary source as a parameter-constant family commutes with
the source-first Hessian four-block. -/
theorem permutedPolynomialHessianFourBlock_constantPolynomialFamily
    (rho : Equiv.Perm (Fin 4)) (F : MvPolynomial (Fin 4) K) :
    permutedPolynomialHessianFourBlock rho (constantPolynomialFamily F) =
      (permutedPolynomialHessianFourBlock rho F).map
        (MvPolynomial.map Polynomial.C) := by
  ext <;>
    simp [permutedPolynomialHessianFourBlock,
      GeneralFourBlock.ofSymmetricMatrix, GeneralFourBlock.map,
      Matrix.submatrix_apply, constantPolynomialFamily,
      HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_map]

@[simp] theorem schurA_constantPolynomialFamily
    (rho : Equiv.Perm (Fin 4)) (F : MvPolynomial (Fin 4) K) :
    (permutedPolynomialHessianFourBlock rho
      (constantPolynomialFamily F)).schurA =
      constantPolynomialFamily
        (permutedPolynomialHessianFourBlock rho F).schurA := by
  have h := congrArg GeneralFourBlock.schurA
    (permutedPolynomialHessianFourBlock_constantPolynomialFamily rho F)
  simpa [constantPolynomialFamily] using h

@[simp] theorem schurB_constantPolynomialFamily
    (rho : Equiv.Perm (Fin 4)) (F : MvPolynomial (Fin 4) K) :
    (permutedPolynomialHessianFourBlock rho
      (constantPolynomialFamily F)).schurB =
      constantPolynomialFamily
        (permutedPolynomialHessianFourBlock rho F).schurB := by
  have h := congrArg GeneralFourBlock.schurB
    (permutedPolynomialHessianFourBlock_constantPolynomialFamily rho F)
  simpa [constantPolynomialFamily] using h

@[simp] theorem schurC_constantPolynomialFamily
    (rho : Equiv.Perm (Fin 4)) (F : MvPolynomial (Fin 4) K) :
    (permutedPolynomialHessianFourBlock rho
      (constantPolynomialFamily F)).schurC =
      constantPolynomialFamily
        (permutedPolynomialHessianFourBlock rho F).schurC := by
  have h := congrArg GeneralFourBlock.schurC
    (permutedPolynomialHessianFourBlock_constantPolynomialFamily rho F)
  simpa [constantPolynomialFamily] using h

/-- Multiplying the source potential by a parameter scalar multiplies each
Hessian entry by that scalar, hence a cleared Schur entry by its cube. -/
theorem schurA_C_mul
    (rho : Equiv.Perm (Fin 4)) (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (permutedPolynomialHessianFourBlock rho
      (MvPolynomial.C c * P)).schurA =
      (MvPolynomial.C c) ^ 3 *
        (permutedPolynomialHessianFourBlock rho P).schurA := by
  unfold permutedPolynomialHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    GeneralFourBlock.schurA GeneralFourBlock.activeDet
  simp [Matrix.submatrix_apply, HC4.Polynomial.hessian_apply,
    MvPolynomial.pderiv_C_mul]
  ring

/-- Scalar cubic covariance for the off-diagonal cleared Schur entry. -/
theorem schurB_C_mul
    (rho : Equiv.Perm (Fin 4)) (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (permutedPolynomialHessianFourBlock rho
      (MvPolynomial.C c * P)).schurB =
      (MvPolynomial.C c) ^ 3 *
        (permutedPolynomialHessianFourBlock rho P).schurB := by
  unfold permutedPolynomialHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    GeneralFourBlock.schurB GeneralFourBlock.activeDet
  simp [Matrix.submatrix_apply, HC4.Polynomial.hessian_apply,
    MvPolynomial.pderiv_C_mul]
  ring

/-- Scalar cubic covariance for the second diagonal cleared Schur entry. -/
theorem schurC_C_mul
    (rho : Equiv.Perm (Fin 4)) (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K)) :
    (permutedPolynomialHessianFourBlock rho
      (MvPolynomial.C c * P)).schurC =
      (MvPolynomial.C c) ^ 3 *
        (permutedPolynomialHessianFourBlock rho P).schurC := by
  unfold permutedPolynomialHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    GeneralFourBlock.schurC GeneralFourBlock.activeDet
  simp [Matrix.submatrix_apply, HC4.Polynomial.hessian_apply,
    MvPolynomial.pderiv_C_mul]
  ring

end

end HC4.Valuation
