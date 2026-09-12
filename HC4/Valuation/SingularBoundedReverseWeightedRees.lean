import HC4.Valuation.BoundedReverseWeightedRees
import Mathlib.Tactic

/-!
# Bounded reverse Rees preserves Hessian singularity

The determinant-one reverse-Rees theorem carries an exact positive Hessian
clock.  For the A19.55 codimension-two opening we need the simpler singular
variant: if the source polynomial has identically zero Hessian determinant,
then every bounded reverse weighted Rees family also has identically zero
Hessian determinant.

The proof uses only the already-verified diagonal-inflation covariance and
injectivity.  No numerical defect is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial

variable {K : Type*} [Field K]

/-- Hessian determinant commutes with extension of source coefficients to the
constant polynomial family. -/
private theorem hessianDeterminant_constantPolynomialFamily
    (F : MvPolynomial (Fin 4) K) :
    HC4.Polynomial.hessianDeterminant (constantPolynomialFamily F) =
      constantPolynomialFamily (HC4.Polynomial.hessianDeterminant F) := by
  let phi :
      MvPolynomial (Fin 4) K →+*
        MvPolynomial (Fin 4) (Polynomial K) :=
    MvPolynomial.map Polynomial.C
  unfold HC4.Polynomial.hessianDeterminant
  rw [show
      HC4.Polynomial.hessian (constantPolynomialFamily F) =
        (HC4.Polynomial.hessian F).map phi by
    ext i j
    simp [constantPolynomialFamily, phi,
      HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_map]]
  exact (phi.map_det (HC4.Polynomial.hessian F)).symm

/-- **Singular reverse-Rees covariance.**  A bounded reverse weighted Rees
family of a Hessian-singular source remains Hessian-singular identically in
the parameter. -/
theorem reverseWeightedReesFamily_hessianDeterminant_eq_zero
    (w : Fin 4 → ℕ) (D : ℕ) (F : MvPolynomial (Fin 4) K)
    (h : HasReverseWeightBound w D F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 0) :
    HC4.Polynomial.hessianDeterminant
      (reverseWeightedReesFamily w D F h) = 0 := by
  let Q := reverseWeightedReesFamily w D F h
  let S := ∑ i : Fin 4, w i
  have hnorm := adaptiveSmithInflate_reverseWeightedReesFamily_eq w D F h
  have hdetEq := congrArg HC4.Polynomial.hessianDeterminant hnorm
  rw [hessianDeterminant_adaptiveSmithInflateHom] at hdetEq
  rw [hessianDeterminant_C_mul] at hdetEq
  rw [hessianDeterminant_constantPolynomialFamily, hdet] at hdetEq
  simp [constantPolynomialFamily] at hdetEq

  have hprod :
      (MvPolynomial.C Polynomial.X :
          MvPolynomial (Fin 4) (Polynomial K)) ^ (2 * S) *
        adaptiveSmithInflateHom w
          (HC4.Polynomial.hessianDeterminant Q) = 0 := by
    dsimp [Q, S] at hdetEq ⊢
    simpa only [map_pow, ← pow_mul, Nat.mul_comm] using hdetEq

  have hfactor :
      (MvPolynomial.C Polynomial.X :
          MvPolynomial (Fin 4) (Polynomial K)) ^ (2 * S) ≠ 0 :=
    pow_ne_zero (2 * S)
      (MvPolynomial.C_ne_zero.mpr Polynomial.X_ne_zero)

  have hinflated :
      adaptiveSmithInflateHom w
          (HC4.Polynomial.hessianDeterminant Q) = 0 :=
    (mul_eq_zero.mp hprod).resolve_left hfactor

  have hzeroInflated :
      adaptiveSmithInflateHom w
          (HC4.Polynomial.hessianDeterminant Q) =
        adaptiveSmithInflateHom w 0 := by
    simpa using hinflated
  exact adaptiveSmithInflateHom_injective w hzeroInflated

end

end HC4.Valuation
