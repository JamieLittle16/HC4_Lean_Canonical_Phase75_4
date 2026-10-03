import HC4.Valuation.WeightedHessianPrincipalMinorInitial
import Mathlib.Tactic

/-!
# Arbitrary Hessian 2x2 minors and maximal weighted initial forms

The existing weighted transport theorem covers principal Hessian minors.  The
canonical coordinate-max opening stores the slightly more general rank-two
witness

    H_ij H_kl - H_il H_kj != 0.

This file proves the identical maximal-initial-form transport for that
arbitrary 2x2 minor.  It is pure weighted polynomial algebra and introduces no
HC4 state, clock, repair, or geometric assumption.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- An arbitrary displayed `2 x 2` minor of the Hessian matrix. -/
def hessianTwoByTwoMinor
    (F : MvPolynomial (Fin 4) K)
    (i j k l : Fin 4) : MvPolynomial (Fin 4) K :=
  HC4.Polynomial.hessian F i j *
      HC4.Polynomial.hessian F k l -
    HC4.Polynomial.hessian F i l *
      HC4.Polynomial.hessian F k j

/-- The maximal weighted component of an arbitrary Hessian `2 x 2` minor
is the corresponding minor of the maximal weighted source component. -/
theorem initialForm_hessianTwoByTwoMinor_eq
    {w : Fin 4 → ℤ} {m : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hF : HC4.Polynomial.IsWeightLE w m F)
    (i j k l : Fin 4) :
    HC4.Polynomial.initialForm w
        ((m - w i - w j) + (m - w k - w l))
        (hessianTwoByTwoMinor F i j k l) =
      hessianTwoByTwoMinor
        (HC4.Polynomial.initialForm w m F) i j k l := by
  have hijLE := hF.hessian_entry i j
  have hklLE := hF.hessian_entry k l
  have hilLE := hF.hessian_entry i l
  have hkjLE := hF.hessian_entry k j
  have hprodLeft :=
    initialForm_mul_eq_mul_initialForm_of_isWeightLE hijLE hklLE
  have hprodRight :=
    initialForm_mul_eq_mul_initialForm_of_isWeightLE hilLE hkjLE
  have hsum :
      (m - w i - w j) + (m - w k - w l) =
        (m - w i - w l) + (m - w k - w j) := by
    ring
  unfold hessianTwoByTwoMinor
  rw [map_sub]
  rw [hprodLeft]
  rw [hsum, hprodRight]
  rw [(HC4.Polynomial.hessian_initialForm_entry w m F i j).symm]
  rw [(HC4.Polynomial.hessian_initialForm_entry w m F k l).symm]
  rw [(HC4.Polynomial.hessian_initialForm_entry w m F i l).symm]
  rw [(HC4.Polynomial.hessian_initialForm_entry w m F k j).symm]

/-- A nonzero arbitrary Hessian minor on a maximal weighted source component
forces the same minor of the whole polynomial to be nonzero. -/
theorem hessianTwoByTwoMinor_ne_zero_of_initialForm_ne_zero
    {w : Fin 4 → ℤ} {m : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hF : HC4.Polynomial.IsWeightLE w m F)
    (i j k l : Fin 4)
    (hminor :
      hessianTwoByTwoMinor
        (HC4.Polynomial.initialForm w m F) i j k l ≠ 0) :
    hessianTwoByTwoMinor F i j k l ≠ 0 := by
  intro hzero
  have htop := congrArg
    (HC4.Polynomial.initialForm w
      ((m - w i - w j) + (m - w k - w l))) hzero
  have htop0 :
      HC4.Polynomial.initialForm w
          ((m - w i - w j) + (m - w k - w l))
          (hessianTwoByTwoMinor F i j k l) = 0 := by
    simpa using htop
  rw [initialForm_hessianTwoByTwoMinor_eq hF i j k l] at htop0
  exact hminor htop0

end

end HC4.Valuation
