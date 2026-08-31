import HC4.Polynomial.RankThreeDegreeOneEulerActiveMinor
import HC4.Valuation.AdaptiveAlignedSmithPureLongitudinalHigherEscape
import Mathlib.Tactic

/-!
# A19.R10: Hessian principal minors and maximal weighted initial forms

The ordinary Hessian entries of a polynomial bounded by weight `m` have the
usual shifted upper bounds.  Therefore the top component of a principal
`2 x 2` Hessian minor is exactly the corresponding minor of the top source
component.

This is the generic algebraic transport needed to lift A19.118's nonzero ray
pivot into the honest A19.117 first superface.  It uses the already-existing
maximal-product initial-form lemma; no new determinant expansion is introduced.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The maximal weighted component of a Hessian principal minor is the
principal minor of the maximal weighted source component. -/
theorem initialForm_hessianPrincipalMinor_eq
    {w : Fin 4 → ℤ} {m : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hF : HC4.Polynomial.IsWeightLE w m F)
    (i j : Fin 4) :
    HC4.Polynomial.initialForm w
        ((m - w i - w i) + (m - w j - w j))
        (HC4.Polynomial.hessianPrincipalMinor F i j) =
      HC4.Polynomial.hessianPrincipalMinor
        (HC4.Polynomial.initialForm w m F) i j := by
  have hiiLE := hF.hessian_entry i i
  have hjjLE := hF.hessian_entry j j
  have hijLE := hF.hessian_entry i j
  have hjiLE := hF.hessian_entry j i
  have hprodDiag :=
    initialForm_mul_eq_mul_initialForm_of_isWeightLE hiiLE hjjLE
  have hprodCross :=
    initialForm_mul_eq_mul_initialForm_of_isWeightLE hijLE hjiLE
  have hsum :
      (m - w i - w i) + (m - w j - w j) =
        (m - w i - w j) + (m - w j - w i) := by
    ring
  unfold HC4.Polynomial.hessianPrincipalMinor
  rw [map_sub]
  rw [hprodDiag]
  rw [hsum, hprodCross]
  rw [(HC4.Polynomial.hessian_initialForm_entry w m F i i).symm]
  rw [(HC4.Polynomial.hessian_initialForm_entry w m F j j).symm]
  rw [(HC4.Polynomial.hessian_initialForm_entry w m F i j).symm]
  rw [(HC4.Polynomial.hessian_initialForm_entry w m F j i).symm]

/-- A nonzero principal pivot on the maximal weighted source component forces
the corresponding principal pivot of the whole polynomial to be nonzero. -/
theorem hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    {w : Fin 4 → ℤ} {m : ℤ}
    {F : MvPolynomial (Fin 4) K}
    (hF : HC4.Polynomial.IsWeightLE w m F)
    (i j : Fin 4)
    (hminor :
      HC4.Polynomial.hessianPrincipalMinor
        (HC4.Polynomial.initialForm w m F) i j ≠ 0) :
    HC4.Polynomial.hessianPrincipalMinor F i j ≠ 0 := by
  intro hzero
  have htop := congrArg
    (HC4.Polynomial.initialForm w
      ((m - w i - w i) + (m - w j - w j))) hzero
  have htop0 :
      HC4.Polynomial.initialForm w
          ((m - w i - w i) + (m - w j - w j))
          (HC4.Polynomial.hessianPrincipalMinor F i j) = 0 := by
    simpa using htop
  rw [initialForm_hessianPrincipalMinor_eq hF i j] at htop0
  exact hminor htop0

end

end HC4.Valuation
