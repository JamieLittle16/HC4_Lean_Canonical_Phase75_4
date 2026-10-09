import HC4.Valuation.QuadraticAxisReverseReesOriginRankTwo
import Mathlib.Tactic

/-!
# Genuine transverse rank-two geometry on the quadratic first-actual face

The represented determinant-one source with marked-axis transverse weight
bounded by two has a reverse-Rees quadratic special fibre.  Although this
face is Hessian-singular in four dimensions, its transverse 3x3 Hessian
block at the origin is IDENTICAL to that of the represented source.

The existing quadratic-axis determinant theorem supplies a nonzero 2x2
minor of this block.  This places a real rank-two witness on the lower
first-actual face itself; it does not confuse source rank-two geometry with
a terminal endpoint or assert a false determinant-one special fibre.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- The three-by-three transverse origin Hessian of the genuine
quadratic reverse-Rees special fibre is the unchanged corresponding
source-origin Hessian. -/
theorem quadraticAxisReverseRees_specialFiber_transverseHessian_entry
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (i k : Fin 3) :
    quadraticFamilyHessianMatrix
        (polynomialFamilySpecialFiber
          (reverseWeightedReesFamily topKernelMarkedAxisNatWeight
            2 F hbound)) i.succ k.succ =
      quadraticFamilyHessianMatrix F i.succ k.succ := by
  let Q := reverseWeightedReesFamily topKernelMarkedAxisNatWeight
    2 F hbound
  change quadraticFamilyHessianMatrix
      (polynomialFamilySpecialFiber Q) i.succ k.succ = _
  rw [polynomialFamilySpecialFiber_reverseWeightedReesFamily_eq_layer_zero
    topKernelMarkedAxisNatWeight 2 F hbound]
  rw [← quadraticFamilyHessianMatrix_coeff_familyParameterLayer
    Q 0 i.succ k.succ]
  rw [quadraticAxisReverseRees_originHessian_entry F hbound i.succ k.succ]
  fin_cases i <;> fin_cases k <;>
    simp [topKernelMarkedAxisNatWeight]

/-- The actual quadratic lower face has a nonzero transverse 2x2
origin-Hessian minor, even though its full 4x4 Hessian determinant is
zero.  The six choices cover all principal and cross 2x2 minors. -/
theorem quadraticAxisReverseRees_specialFiber_transverseRankTwo
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    let G := polynomialFamilySpecialFiber
      (reverseWeightedReesFamily topKernelMarkedAxisNatWeight
        2 F hbound)
    let H := quadraticFamilyHessianMatrix G
    H 2 2 * H 3 3 - H 2 3 * H 2 3 ≠ 0 ∨
    H 1 2 * H 3 3 - H 1 3 * H 2 3 ≠ 0 ∨
    H 1 2 * H 2 3 - H 1 3 * H 2 2 ≠ 0 ∨
    H 1 1 * H 3 3 - H 1 3 * H 1 3 ≠ 0 ∨
    H 1 1 * H 2 3 - H 1 2 * H 1 3 ≠ 0 ∨
    H 1 1 * H 2 2 - H 1 2 * H 1 2 ≠ 0 := by
  let G := polynomialFamilySpecialFiber
    (reverseWeightedReesFamily topKernelMarkedAxisNatWeight 2 F hbound)
  let H := quadraticFamilyHessianMatrix G
  have h11 : H 1 1 = quadraticFamilyHessianMatrix F 1 1 := by
    simpa only [H, G] using
      (quadraticAxisReverseRees_specialFiber_transverseHessian_entry
        F hbound (0 : Fin 3) (0 : Fin 3))
  have h12 : H 1 2 = quadraticFamilyHessianMatrix F 1 2 := by
    simpa only [H, G] using
      (quadraticAxisReverseRees_specialFiber_transverseHessian_entry
        F hbound (0 : Fin 3) (1 : Fin 3))
  have h13 : H 1 3 = quadraticFamilyHessianMatrix F 1 3 := by
    simpa only [H, G] using
      (quadraticAxisReverseRees_specialFiber_transverseHessian_entry
        F hbound (0 : Fin 3) (2 : Fin 3))
  have h22 : H 2 2 = quadraticFamilyHessianMatrix F 2 2 := by
    simpa only [H, G] using
      (quadraticAxisReverseRees_specialFiber_transverseHessian_entry
        F hbound (1 : Fin 3) (1 : Fin 3))
  have h23 : H 2 3 = quadraticFamilyHessianMatrix F 2 3 := by
    simpa only [H, G] using
      (quadraticAxisReverseRees_specialFiber_transverseHessian_entry
        F hbound (1 : Fin 3) (2 : Fin 3))
  have h33 : H 3 3 = quadraticFamilyHessianMatrix F 3 3 := by
    simpa only [H, G] using
      (quadraticAxisReverseRees_specialFiber_transverseHessian_entry
        F hbound (2 : Fin 3) (2 : Fin 3))
  change
    H 2 2 * H 3 3 - H 2 3 * H 2 3 ≠ 0 ∨
    H 1 2 * H 3 3 - H 1 3 * H 2 3 ≠ 0 ∨
    H 1 2 * H 2 3 - H 1 3 * H 2 2 ≠ 0 ∨
    H 1 1 * H 3 3 - H 1 3 * H 1 3 ≠ 0 ∨
    H 1 1 * H 2 3 - H 1 2 * H 1 3 ≠ 0 ∨
    H 1 1 * H 2 2 - H 1 2 * H 1 2 ≠ 0
  rw [h11, h12, h13, h22, h23, h33]
  exact quadraticAxisReverseRees_sourceTransverseRankTwo F hbound hdet

end

end HC4.Valuation
