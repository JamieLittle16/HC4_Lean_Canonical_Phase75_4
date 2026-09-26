import HC4.Valuation.BoundedReverseWeightedRees
import Mathlib.Tactic

/-!
# Arbitrary 2 x 2 Hessian minors under bounded reverse Rees inflation

The existing principal-minor lift is sufficient when the same two source
coordinates occur as both row and column indices.  The projected 1+3
first-break geometry also naturally produces mixed 2 x 2 Hessian minors.

For four source indices `i,j,k,l`, define

    H_ik H_jl - H_il H_jk.

Under diagonal source inflation both products acquire the identical factor
`X^(w_i+w_j+w_k+w_l)`.  Hence nonvanishing of any whole-family 2 x 2
Hessian minor of a bounded reverse-Rees family lifts back to the represented
source exactly as in the principal case.

No layerwise noncancellation is asserted here: the input is nonvanishing of
the whole-family minor.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial

universe u
variable {K : Type u} [Field K]

/-- Arbitrary two-row/two-column Hessian minor. -/
def hessianTwoByTwoMinor
    (P : MvPolynomial (Fin 4) K)
    (i j k l : Fin 4) : MvPolynomial (Fin 4) K :=
  HC4.Polynomial.hessian P i k * HC4.Polynomial.hessian P j l -
    HC4.Polynomial.hessian P i l * HC4.Polynomial.hessian P j k

/-- The same minor for a parameter-polynomial family. -/
def familyHessianTwoByTwoMinor
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i j k l : Fin 4) : MvPolynomial (Fin 4) (Polynomial K) :=
  HC4.Polynomial.hessian P i k * HC4.Polynomial.hessian P j l -
    HC4.Polynomial.hessian P i l * HC4.Polynomial.hessian P j k

/-- Arbitrary Hessian minors transform covariantly under diagonal source
inflation. -/
theorem familyHessianTwoByTwoMinor_adaptiveSmithInflateHom
    (W : Fin 4 → ℕ)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i j k l : Fin 4) :
    familyHessianTwoByTwoMinor (adaptiveSmithInflateHom W P) i j k l =
      (MvPolynomial.C (Polynomial.X ^ W i) *
          MvPolynomial.C (Polynomial.X ^ W j) *
          MvPolynomial.C (Polynomial.X ^ W k) *
          MvPolynomial.C (Polynomial.X ^ W l)) *
        adaptiveSmithInflateHom W
          (familyHessianTwoByTwoMinor P i j k l) := by
  unfold familyHessianTwoByTwoMinor
  rw [hessian_adaptiveSmithInflateHom_entry,
    hessian_adaptiveSmithInflateHom_entry,
    hessian_adaptiveSmithInflateHom_entry,
    hessian_adaptiveSmithInflateHom_entry]
  simp only [map_sub, map_mul]
  ring

/-- Multiplication by a parameter scalar squares that scalar in every
arbitrary 2 x 2 Hessian minor. -/
theorem familyHessianTwoByTwoMinor_C_mul
    (c : Polynomial K)
    (P : MvPolynomial (Fin 4) (Polynomial K))
    (i j k l : Fin 4) :
    familyHessianTwoByTwoMinor (MvPolynomial.C c * P) i j k l =
      (MvPolynomial.C c) ^ 2 *
        familyHessianTwoByTwoMinor P i j k l := by
  unfold familyHessianTwoByTwoMinor HC4.Polynomial.hessian
  simp only [Matrix.of_apply, MvPolynomial.pderiv_C_mul]
  ring

/-- Constant polynomial-family embedding commutes with arbitrary Hessian
2 x 2 minors. -/
theorem familyHessianTwoByTwoMinor_constantPolynomialFamily
    (F : MvPolynomial (Fin 4) K)
    (i j k l : Fin 4) :
    familyHessianTwoByTwoMinor (constantPolynomialFamily F) i j k l =
      MvPolynomial.map Polynomial.C
        (hessianTwoByTwoMinor F i j k l) := by
  unfold familyHessianTwoByTwoMinor hessianTwoByTwoMinor
    constantPolynomialFamily
  simp [HC4.Polynomial.hessian_apply, MvPolynomial.pderiv_map]

/-- **Whole-family reverse-Rees arbitrary-minor lift.**

A nonzero arbitrary 2 x 2 Hessian minor on the honest bounded reverse-Rees
family forces the corresponding represented-source minor to be nonzero. -/
theorem reverseWeightedReesFamily_sourceTwoByTwoMinor_of_familyMinor_ne_zero
    (w : Fin 4 → ℕ)
    (D : ℕ)
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound w D F)
    (i j k l : Fin 4)
    (hminor :
      familyHessianTwoByTwoMinor
        (reverseWeightedReesFamily w D F hbound) i j k l ≠ 0) :
    hessianTwoByTwoMinor F i j k l ≠ 0 := by
  let Q := reverseWeightedReesFamily w D F hbound
  intro hsource
  have hnorm :=
    adaptiveSmithInflate_reverseWeightedReesFamily_eq w D F hbound
  have hminorEq := congrArg
    (fun R : MvPolynomial (Fin 4) (Polynomial K) =>
      familyHessianTwoByTwoMinor R i j k l) hnorm
  change
    familyHessianTwoByTwoMinor
        (adaptiveSmithInflateHom w
          (reverseWeightedReesFamily w D F hbound)) i j k l =
      familyHessianTwoByTwoMinor
        (MvPolynomial.C (Polynomial.X ^ D) *
          constantPolynomialFamily F) i j k l at hminorEq
  rw [familyHessianTwoByTwoMinor_adaptiveSmithInflateHom,
    familyHessianTwoByTwoMinor_C_mul,
    familyHessianTwoByTwoMinor_constantPolynomialFamily,
    hsource] at hminorEq
  simp only [map_zero, mul_zero] at hminorEq
  let vi : MvPolynomial (Fin 4) (Polynomial K) :=
    MvPolynomial.C (Polynomial.X ^ w i)
  let vj : MvPolynomial (Fin 4) (Polynomial K) :=
    MvPolynomial.C (Polynomial.X ^ w j)
  let vk : MvPolynomial (Fin 4) (Polynomial K) :=
    MvPolynomial.C (Polynomial.X ^ w k)
  let vl : MvPolynomial (Fin 4) (Polynomial K) :=
    MvPolynomial.C (Polynomial.X ^ w l)
  have hvi : vi ≠ 0 := by
    dsimp [vi]
    exact MvPolynomial.C_ne_zero.mpr
      (pow_ne_zero _ Polynomial.X_ne_zero)
  have hvj : vj ≠ 0 := by
    dsimp [vj]
    exact MvPolynomial.C_ne_zero.mpr
      (pow_ne_zero _ Polynomial.X_ne_zero)
  have hvk : vk ≠ 0 := by
    dsimp [vk]
    exact MvPolynomial.C_ne_zero.mpr
      (pow_ne_zero _ Polynomial.X_ne_zero)
  have hvl : vl ≠ 0 := by
    dsimp [vl]
    exact MvPolynomial.C_ne_zero.mpr
      (pow_ne_zero _ Polynomial.X_ne_zero)
  have hfactor : vi * vj * vk * vl ≠ 0 :=
    mul_ne_zero (mul_ne_zero (mul_ne_zero hvi hvj) hvk) hvl
  have hinflatedZero :
      adaptiveSmithInflateHom w
          (familyHessianTwoByTwoMinor Q i j k l) = 0 := by
    have hprod :
        (vi * vj * vk * vl) *
            adaptiveSmithInflateHom w
              (familyHessianTwoByTwoMinor Q i j k l) = 0 := by
      simpa [Q, vi, vj, vk, vl] using hminorEq
    exact (mul_eq_zero.mp hprod).resolve_left hfactor
  have hQzero :
      familyHessianTwoByTwoMinor Q i j k l = 0 := by
    apply adaptiveSmithInflateHom_injective w
    simpa using hinflatedZero
  exact hminor (by simpa [Q] using hQzero)

end

end HC4.Valuation
