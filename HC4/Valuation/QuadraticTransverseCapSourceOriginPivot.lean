import HC4.Valuation.QuadraticTransverseCapSourceSections
import HC4.Valuation.QuadraticAxisReverseReesOriginRankTwo
import Mathlib.Tactic

/-!
# Source-origin transverse rank two is genuinely polynomial on the marked axis

The actual quadratic reverse-Rees source has a six-way nonzero transverse
2x2 origin-Hessian minor. The SOURCE-AXIS transverse block C(x) is a
matrix of polynomials, not a pointwise numerical Hessian. Its evaluation
at x=0 is exactly the original source-origin transverse Hessian.

Therefore the genuine source-origin witness gives a NONZERO POLYNOMIAL
2x2 minor of C, and permits a generic rank-two/rank-three split over
the polynomial coefficient domain. No associated-graded rank is confused
with the represented source.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

/- Avoid imported simp rewrites of raw pderiv 2/3 into two-zero aliases when
   matching the literal origin Hessian entries. -/
attribute [-simp] standardTwoZero_pderiv_two_eq_A
attribute [-simp] standardTwoZero_pderiv_three_eq_C

variable {K : Type*} [Field K]

/-- Evaluation at the longitudinal origin of the axis-restricted
source Hessian is exactly the original four-variable source-origin
Hessian coefficient. -/
theorem quadraticTransverseCapSource_axisHessian_origin
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 4) :
    Polynomial.eval (0 : K)
      (((HC4.Polynomial.hessian F).map
        (longitudinalAxisRestrictionRingHom (K := K))) i j) =
      quadraticFamilyHessianMatrix F i j := by
  rw [Matrix.map_apply, longitudinalAxisRestrictionRingHom_apply]
  rw [← eval_finCons_zero_eq_longitudinalAxisRestriction]
  change
    MvPolynomial.eval
      (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
      (MvPolynomial.pderiv j (MvPolynomial.pderiv i F)) =
    MvPolynomial.constantCoeff
      (MvPolynomial.pderiv j (MvPolynomial.pderiv i F))
  have hzero :
      (Fin.cons (0 : K) (fun _ : Fin 3 => 0)) =
        (fun _ : Fin 4 => (0 : K)) := by
    funext k
    fin_cases k <;> rfl
  rw [hzero, MvPolynomial.eval_zero', MvPolynomial.constantCoeff_eq]

/-- All entries of the ACTUAL polynomial transverse Hessian block,
evaluated at x=0, equal the corresponding original source-origin
transverse Hessian entries. -/
theorem quadraticTransverseCapSource_axisThreeBlock_origin
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 3) :
    Polynomial.eval (0 : K)
      ((quadraticTransverseCapSourceAxisThreeBlock F).matrix i j) =
      quadraticFamilyHessianMatrix F i.succ j.succ := by
  fin_cases i <;> fin_cases j <;>
    simpa [quadraticTransverseCapSourceAxisThreeBlock,
      quadraticTransverseCapSourceAxisFourBlock,
      GeneralThreeBlock.matrix, GeneralFourBlock.ofSymmetricMatrix] using
      (quadraticTransverseCapSource_axisHessian_origin F _ _)

/-- The source-origin nonzero transverse 2x2 Hessian minor genuinely lifts
to a nonzero POLYNOMIAL 2x2 minor of the actual longitudinal-axis
three-block. In particular C(x) has generic rank at least two.

This is not yet a chosen principal pivot; the finite source shear
alternative must be propagated to C to obtain that later normal form. -/
theorem quadraticTransverseCapSource_axisThreeBlock_polynomialRankTwo
    [CharZero K]
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    let C := quadraticTransverseCapSourceAxisThreeBlock F
    C.d * C.f - C.e * C.e ≠ 0 ∨
    C.b * C.f - C.c * C.e ≠ 0 ∨
    C.b * C.e - C.c * C.d ≠ 0 ∨
    C.a * C.f - C.c * C.c ≠ 0 ∨
    C.a * C.e - C.b * C.c ≠ 0 ∨
    C.a * C.d - C.b * C.b ≠ 0 := by
  let C := quadraticTransverseCapSourceAxisThreeBlock F
  let H := quadraticFamilyHessianMatrix F
  have ha : Polynomial.eval (0 : K) C.a = H 1 1 := by
    simpa [C, H, quadraticTransverseCapSourceAxisThreeBlock,
      quadraticTransverseCapSourceAxisFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (quadraticTransverseCapSource_axisHessian_origin F 1 1)
  have hb : Polynomial.eval (0 : K) C.b = H 1 2 := by
    simpa [C, H, quadraticTransverseCapSourceAxisThreeBlock,
      quadraticTransverseCapSourceAxisFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (quadraticTransverseCapSource_axisHessian_origin F 1 2)
  have hc : Polynomial.eval (0 : K) C.c = H 1 3 := by
    simpa [C, H, quadraticTransverseCapSourceAxisThreeBlock,
      quadraticTransverseCapSourceAxisFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (quadraticTransverseCapSource_axisHessian_origin F 1 3)
  have hd : Polynomial.eval (0 : K) C.d = H 2 2 := by
    simpa [C, H, quadraticTransverseCapSourceAxisThreeBlock,
      quadraticTransverseCapSourceAxisFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (quadraticTransverseCapSource_axisHessian_origin F 2 2)
  have he : Polynomial.eval (0 : K) C.e = H 2 3 := by
    simpa [C, H, quadraticTransverseCapSourceAxisThreeBlock,
      quadraticTransverseCapSourceAxisFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (quadraticTransverseCapSource_axisHessian_origin F 2 3)
  have hf : Polynomial.eval (0 : K) C.f = H 3 3 := by
    simpa [C, H, quadraticTransverseCapSourceAxisThreeBlock,
      quadraticTransverseCapSourceAxisFourBlock,
      GeneralFourBlock.ofSymmetricMatrix] using
      (quadraticTransverseCapSource_axisHessian_origin F 3 3)
  have hlift (p q r s : Polynomial K)
      (h :
        Polynomial.eval (0 : K) p * Polynomial.eval (0 : K) q -
          Polynomial.eval (0 : K) r * Polynomial.eval (0 : K) s ≠ 0) :
      p * q - r * s ≠ 0 := by
    intro hz
    have hmap := congrArg (Polynomial.eval (0 : K)) hz
    apply h
    simpa only [Polynomial.eval_sub, Polynomial.eval_mul,
      Polynomial.eval_zero] using hmap
  have hsource :=
    quadraticAxisReverseRees_sourceTransverseRankTwo F hbound hdet
  dsimp only at hsource ⊢
  rcases hsource with hm | hm | hm | hm | hm | hm
  · exact Or.inl (hlift C.d C.f C.e C.e (by
      simpa only [hd, hf, he] using hm))
  · exact Or.inr (Or.inl (hlift C.b C.f C.c C.e (by
      simpa only [hb, hf, hc, he] using hm)))
  · exact Or.inr (Or.inr (Or.inl (hlift C.b C.e C.c C.d (by
      simpa only [hb, he, hc, hd] using hm))))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (hlift C.a C.f C.c C.c (by
      simpa only [ha, hf, hc] using hm)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
      (hlift C.a C.e C.b C.c (by
        simpa only [ha, he, hb, hc] using hm))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr
      (hlift C.a C.d C.b C.b (by
        simpa only [ha, hd, hb] using hm))))))

end

end HC4.Valuation
