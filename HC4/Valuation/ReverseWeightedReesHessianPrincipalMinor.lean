import HC4.Valuation.BoundedReverseWeightedRees
import HC4.Polynomial.RankThreeDegreeOneEulerActiveMinor
import Mathlib.Tactic

/-!
# Principal Hessian minors under bounded reverse Rees inflation

A nonzero coefficient of a whole-family principal Hessian minor of a bounded
reverse weighted Rees family is stronger than an auxiliary layer event.  The
diagonal source inflation used to normalize the reverse Rees family acts on a
principal (2\times2) Hessian minor by one explicit nonzero parameter
monomial.  Since the inflation homomorphism is injective, nonvanishing of the
whole-family minor lifts back to the represented source.

This file deliberately says nothing about a principal minor formed from one
individual parameter layer: cross-layer products may contribute at the same
total order, so that separate case needs its own argument.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial

universe u
variable {K : Type u} [Field K]

/-- Principal (2\times2) Hessian minors transform covariantly under the
adaptive diagonal source inflation. -/
theorem hessianPrincipalMinor_adaptiveSmithInflateHom
    (W : Fin 4 → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4) :
    HC4.Polynomial.hessianPrincipalMinor
        (adaptiveSmithInflateHom W P) i j =
      (MvPolynomial.C (Polynomial.X ^ W i) *
          MvPolynomial.C (Polynomial.X ^ W j)) ^ 2 *
        adaptiveSmithInflateHom W
          (HC4.Polynomial.hessianPrincipalMinor P i j) := by
  unfold HC4.Polynomial.hessianPrincipalMinor
  rw [hessian_adaptiveSmithInflateHom_entry,
    hessian_adaptiveSmithInflateHom_entry,
    hessian_adaptiveSmithInflateHom_entry,
    hessian_adaptiveSmithInflateHom_entry]
  simp only [map_sub, map_mul]
  ring

/-- Multiplying a source polynomial by a source-independent parameter scalar
squares that scalar in every principal (2\times2) Hessian minor. -/
theorem hessianPrincipalMinor_C_mul
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i j : Fin 4) :
    HC4.Polynomial.hessianPrincipalMinor
        (MvPolynomial.C c * P) i j =
      (MvPolynomial.C c) ^ 2 *
        HC4.Polynomial.hessianPrincipalMinor P i j := by
  unfold HC4.Polynomial.hessianPrincipalMinor HC4.Polynomial.hessian
  simp only [Matrix.of_apply, MvPolynomial.pderiv_C_mul]
  ring

/-- Embedding source coefficients into the parameter-polynomial ring commutes
with principal Hessian minors. -/
theorem hessianPrincipalMinor_constantPolynomialFamily
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 4) :
    HC4.Polynomial.hessianPrincipalMinor
        (constantPolynomialFamily F) i j =
      MvPolynomial.map Polynomial.C
        (HC4.Polynomial.hessianPrincipalMinor F i j) := by
  unfold HC4.Polynomial.hessianPrincipalMinor constantPolynomialFamily
  simp [HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_map]

/-- **Whole-family reverse-Rees principal-minor lift.**

If a principal Hessian minor of the honest bounded reverse-Rees family is
nonzero as a polynomial in the Rees parameter, then the corresponding
principal minor of the represented source is already nonzero.  The proof uses
the exact whole-family normalization and injectivity of the diagonal source
inflation, so no specialization of the Rees parameter is involved. -/
theorem reverseWeightedReesFamily_sourceMinor_of_familyMinor_ne_zero
    (w : Fin 4 → ℕ)
    (D : ℕ)
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound w D F)
    (i j : Fin 4)
    (hminor :
      HC4.Polynomial.hessianPrincipalMinor
        (reverseWeightedReesFamily w D F hbound) i j ≠ 0) :
    HC4.Polynomial.hessianPrincipalMinor F i j ≠ 0 := by
  let Q := reverseWeightedReesFamily w D F hbound
  intro hsource
  have hnorm :=
    adaptiveSmithInflate_reverseWeightedReesFamily_eq w D F hbound
  have hminorEq := congrArg
    (fun R : MvPolynomial (Fin 4) (Polynomial K) =>
      HC4.Polynomial.hessianPrincipalMinor R i j) hnorm
  rw [hessianPrincipalMinor_adaptiveSmithInflateHom,
    hessianPrincipalMinor_C_mul,
    hessianPrincipalMinor_constantPolynomialFamily,
    hsource] at hminorEq
  simp only [map_zero, mul_zero] at hminorEq
  let vi : MvPolynomial (Fin 4) (Polynomial K) :=
    MvPolynomial.C (Polynomial.X ^ w i)
  let vj : MvPolynomial (Fin 4) (Polynomial K) :=
    MvPolynomial.C (Polynomial.X ^ w j)
  have hvi : vi ≠ 0 := by
    dsimp [vi]
    exact MvPolynomial.C_ne_zero.mpr
      (pow_ne_zero _ Polynomial.X_ne_zero)
  have hvj : vj ≠ 0 := by
    dsimp [vj]
    exact MvPolynomial.C_ne_zero.mpr
      (pow_ne_zero _ Polynomial.X_ne_zero)
  have hfactor : (vi * vj) ^ 2 ≠ 0 :=
    pow_ne_zero _ (mul_ne_zero hvi hvj)
  have hinflatedZero :
      adaptiveSmithInflateHom w
          (HC4.Polynomial.hessianPrincipalMinor Q i j) = 0 := by
    have hprod :
        (vi * vj) ^ 2 *
            adaptiveSmithInflateHom w
              (HC4.Polynomial.hessianPrincipalMinor Q i j) = 0 := by
      simpa [Q, vi, vj] using hminorEq
    exact (mul_eq_zero.mp hprod).resolve_left hfactor
  have hQzero :
      HC4.Polynomial.hessianPrincipalMinor Q i j = 0 := by
    apply adaptiveSmithInflateHom_injective w
    simpa using hinflatedZero
  exact hminor (by simpa [Q] using hQzero)

end

end HC4.Valuation
