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

end

end HC4.Valuation
