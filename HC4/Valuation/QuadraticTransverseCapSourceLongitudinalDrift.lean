import HC4.Valuation.QuadraticTransverseCapRankThreeLongitudinalDrift
import HC4.Valuation.QuadraticTransverseCapSourceSchurProfile
import Mathlib.Tactic

/-!
# Source-honest longitudinal closing endpoint in rank-three quadratic cap

The actual represented source already has a collision between 0 and e₀.
Its longitudinal axis coefficient a(x)=F(x,0) therefore satisfies
a'(1)=a'(0), without any associated-graded replacement.

If the rank-three reciprocal-matrix analysis yields constant
nonzero det C and zero transverse-linear derivative b', then
the actual axis Hessian determinant-one equation gives
    det(C) * a'' = 1.
This is impossible by exact marked longitudinal collision.

The remaining inverse-matrix ODE normal form must *derive*
the two inputs (constant det C and b'=0); they are not asserted
here for an arbitrary generic-rank-three source.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K] [CharZero K]

/-- Actual marked collision on the source yields the required
equality of the source's longitudinal axis derivative at
x=0 and x=1, with no extra gradient normalization. -/
theorem quadraticTransverse_source_longitudinalMarkedCollision
    (F : MvPolynomial (Fin 4) K)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0))) :
    Polynomial.eval (1 : K)
        (Polynomial.derivative (longitudinalAxisRestriction F)) =
      Polynomial.eval (0 : K)
        (Polynomial.derivative (longitudinalAxisRestriction F)) := by
  rw [← eval_pderiv_zero_finCons_zero_eq_eval_axisRestriction_derivative,
    ← eval_pderiv_zero_finCons_zero_eq_eval_axisRestriction_derivative]
  exact (hcoll (0 : Fin 4)).symm

/-- The actual source-axis longitudinal Hessian is exactly a''(x)
for a(x)=F(x,0), as a polynomial identity. -/
theorem quadraticTransverse_source_axisLongitudinalHessian
    (F : MvPolynomial (Fin 4) K) :
    (quadraticTransverseCapSourceAxisFourBlock F).a =
      Polynomial.derivative
        (Polynomial.derivative (longitudinalAxisRestriction F)) := by
  change longitudinalAxisRestriction
      (MvPolynomial.pderiv (0 : Fin 4)
        (MvPolynomial.pderiv (0 : Fin 4) F)) =
    Polynomial.derivative
      (Polynomial.derivative (longitudinalAxisRestriction F))
  rw [longitudinalAxisRestriction_pderiv_zero]
  rw [longitudinalAxisRestriction_pderiv_zero]

/-- The actual source gives a final contradiction if the
rank-three matrix normal form has produced two CONCRETE
polynomial consequences:
 (i) nonzero constant transverse determinant,
 (ii) zero three-component mixed derivative.

Both consequences must still be extracted from the source
inverse-affine ODE. There is no final-resolution producer in
this theorem. -/
theorem quadraticTransverseCap_two_rankThree_constantDetZeroMixed_impossible
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (d : K)
    (hd : d ≠ 0)
    (hCdet :
      (quadraticTransverseCapSourceAxisThreeBlock F).determinantCore =
        Polynomial.C d)
    (hbmixed : ∀ i : Fin 3,
      Polynomial.derivative
        (quadraticTransverseCapSourceLinearCoefficients F i) = 0)
    (hcoll :
      HasExactGradientCollision F
        (Fin.cons (0 : K) (fun _ : Fin 3 => 0))
        (Fin.cons (1 : K) (fun _ : Fin 3 => 0))) :
    False := by
  let H := quadraticTransverseCapSourceAxisFourBlock F
  let C := quadraticTransverseCapSourceAxisThreeBlock F
  let b := quadraticTransverseCapSourceLinearCoefficients F
  let a := longitudinalAxisRestriction F
  have haxis :
      quadraticAxisFourBlockCore H.a
        (Polynomial.derivative (b 0))
        (Polynomial.derivative (b 1))
        (Polynomial.derivative (b 2))
        C.a C.b C.c C.d C.e C.f = 1 :=
    quadraticTransverseCapSource_axisSchur_unit F hdet
  have hproduct : H.a * C.determinantCore = 1 := by
    rw [hbmixed 0, hbmixed 1, hbmixed 2] at haxis
    unfold quadraticAxisFourBlockCore at haxis
    unfold GeneralThreeBlock.determinantCore
    linear_combination haxis
  have hsecond : Polynomial.C d *
      Polynomial.derivative (Polynomial.derivative a) = 1 := by
    rw [← quadraticTransverse_source_axisLongitudinalHessian F]
    change Polynomial.C d * H.a = 1
    rw [← hCdet]
    linear_combination hproduct
  have hmark := quadraticTransverse_source_longitudinalMarkedCollision
    F hcoll
  exact quadraticTransverse_rankThree_constantDet_longitudinalCollision_impossible
    a d hd hsecond hmark

end

end HC4.Valuation
