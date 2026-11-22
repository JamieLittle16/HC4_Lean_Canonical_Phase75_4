import HC4.Polynomial.RankThreeCubicDetOneWeightFiveDeterminantFirstVariation
import HC4.Polynomial.RankThreeCubicDetOneWeightFiveSourceGap
import Mathlib.Tactic

/-!
# The actual source-derived weight-five adjugate constraint

For a represented source polynomial F of transverse cubic weight <= 3,
let L3 and L2 be its ACTUAL exact weight-3 and weight-2 initial
forms. The weight-five component of det Hess(F) is exactly

  tr(adj(Hess(L3)) * Hess(L2)).

There is no independent generic-matrix or rank assumption. In
particular, if det Hess(F) = 1 this pairing must vanish.

The leading cubic Hessian is permitted to be singular. This proves
a necessary source constraint, not yet a contradiction to a pole.
-/

namespace HC4.Polynomial.RankThreeCubic

open MvPolynomial
open scoped BigOperators
noncomputable section

variable {K : Type*} [Field K]
private abbrev SB (K : Type*) [Field K] := MvPolynomial (Unit ⊕ Fin 3) K

/-- An exact formula for the first lower weight component of the
original source's Hessian determinant, using only its actual cubic
and quadratic initial forms. -/
theorem sourceCubic_weightFive_det_eq_adjugate_pairing
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F) :
    initialForm transverseCubicWeight 5 (hessianDeterminant F) =
      ((hessian (initialForm transverseCubicWeight 3 F)).adjugate *
        hessian (initialForm transverseCubicWeight 2 F)).trace := by
  classical
  let w := transverseCubicWeight
  have hweights (π : Equiv.Perm (Unit ⊕ Fin 3)) :
      (∑ i : Unit ⊕ Fin 3,
        (3 - w (π i) - w i : ℤ)) = 6 := by
    have h := hessianTermWeight_eq w 3 π
    have hd :
        (Fintype.card (Unit ⊕ Fin 3) : ℤ) * 3 -
          2 * ∑ i : Unit ⊕ Fin 3, w i = 6 := by
      decide
    exact h.trans hd
  have hA (i j : Unit ⊕ Fin 3) :
      hessian (initialForm w 3 F) i j =
        initialForm w (3 - w i - w j) (hessian F i j) :=
    hessian_initialForm_entry w 3 F i j
  have hB (i j : Unit ⊕ Fin 3) :
      hessian (initialForm w 2 F) i j =
        initialForm w ((3 - w i - w j) - 1) (hessian F i j) := by
    have h := hessian_initialForm_entry w 2 F i j
    convert h using 1 <;> ring
  have hfirst := initialForm_det_first_lower_eq_adjugate_trace
    (σ := Unit ⊕ Fin 3) (ι := Unit ⊕ Fin 3)
    w 6 (fun i j : Unit ⊕ Fin 3 => 3 - w i - w j)
    (hessian F)
    (hessian (initialForm w 3 F))
    (hessian (initialForm w 2 F))
    hweights
    (fun i j => hcap.hessian_entry i j)
    hA hB
  change initialForm w 5 (hessian F).det =
    ((hessian (initialForm w 3 F)).adjugate *
      hessian (initialForm w 2 F)).trace
  simpa only [show (6 : ℤ) - 1 = 5 by norm_num] using hfirst

/-- If the actual represented four-variable source has constant
Hessian determinant one, its quadratic transverse source layer
satisfies the adjugate constraint imposed by the cubic layer. -/
theorem sourceCubic_detOne_firstCorrection_adjugate_trace_zero
    (F : SB K)
    (hcap : IsWeightLE transverseCubicWeight 3 F)
    (hdetOne : hessianDeterminant F = 1) :
    ((hessian (initialForm transverseCubicWeight 3 F)).adjugate *
      hessian (initialForm transverseCubicWeight 2 F)).trace = 0 := by
  have hfirst := sourceCubic_weightFive_det_eq_adjugate_pairing F hcap
  rw [sourceCubic_detOne_weightFive_initialForm_zero F hdetOne] at hfirst
  exact hfirst.symm

end
end HC4.Polynomial.RankThreeCubic
