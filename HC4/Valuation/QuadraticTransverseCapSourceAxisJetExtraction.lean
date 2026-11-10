import HC4.Valuation.QuadraticTransverseCapSourceAxisMixedDerivative
import Mathlib.Tactic

/-!
# Genuine quadratic source: the three axis adjugate derivative jets

The source Hessian determinant-one equation, differentiated in any of
the three transverse variables, restricts to a polynomial equality
along the longitudinal axis. Under det(C)=0, its longitudinal
Hessian derivative term vanishes. The remaining factor of two is
cancelled in characteristic zero.

Commutation of the genuine third source partials identifies each
mixed-entry transverse derivative with a longitudinal derivative of
a transverse-block entry. The resulting theorem produces the source
jet needed for the pivot-free rank-two kernel proof, for an arbitrary
transverse index, without seven additional section hypotheses.
-/

namespace HC4.Valuation

noncomputable section
open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- The derivative of the actual Schur equation gives the adjugate
axis jet for EVERY transverse direction when the transverse Hessian
three-block has vanishing determinant on the marked axis. -/
theorem quadraticSource_rankTwo_axisAdjugateJet_zero
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (hthree : (quadraticSourceAxisThreeBlock F).determinantCore = 0)
    (i : Fin 3) :
    let C := quadraticSourceAxisThreeBlock F
    let b : Fin 3 → Polynomial K :=
      fun j => longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F
    Polynomial.derivative
        (quadraticSourceSectionHessian F (fun _ : Fin 3 => 0)
          i.succ (0 : Fin 3).succ) *
        quadraticTransverseAdjugateVector0 C
          (Polynomial.derivative (b 0))
          (Polynomial.derivative (b 1))
          (Polynomial.derivative (b 2)) +
      Polynomial.derivative
        (quadraticSourceSectionHessian F (fun _ : Fin 3 => 0)
          i.succ (1 : Fin 3).succ) *
        quadraticTransverseAdjugateVector1 C
          (Polynomial.derivative (b 0))
          (Polynomial.derivative (b 1))
          (Polynomial.derivative (b 2)) +
      Polynomial.derivative
        (quadraticSourceSectionHessian F (fun _ : Fin 3 => 0)
          i.succ (2 : Fin 3).succ) *
        quadraticTransverseAdjugateVector2 C
          (Polynomial.derivative (b 0))
          (Polynomial.derivative (b 1))
          (Polynomial.derivative (b 2)) = 0 := by
  dsimp only
  let H := HC4.Polynomial.hessian F
  let D : GeneralThreeBlock (MvPolynomial (Fin 4) K) :=
    { a := H 1 1, b := H 1 2, c := H 1 3,
      d := H 2 2, e := H 2 3, f := H 3 3 }
  let C := quadraticSourceAxisThreeBlock F
  let b : Fin 3 → Polynomial K :=
    fun j => longitudinalCoefficientPolynomialAt (Finsupp.single j 1) F
  let f := quadraticSourceSectionRingHom (K := K)
    (fun _ : Fin 3 => (0 : K))
  have hv₀ : f (H 0 1) = Polynomial.derivative (b 0) :=
    quadraticSourceSectionHessian_axis_mixed F 0
  have hv₁ : f (H 0 2) = Polynomial.derivative (b 1) :=
    quadraticSourceSectionHessian_axis_mixed F 1
  have hv₂ : f (H 0 3) = Polynomial.derivative (b 2) :=
    quadraticSourceSectionHessian_axis_mixed F 2
  have hmapdet : f D.determinantCore = C.determinantCore := by
    change
      f (D.a * D.d * D.f + 2 * D.b * D.c * D.e -
        D.a * D.e * D.e - D.d * D.c * D.c - D.f * D.b * D.b) =
      f D.a * f D.d * f D.f + 2 * f D.b * f D.c * f D.e -
        f D.a * f D.e * f D.e - f D.d * f D.c * f D.c -
          f D.f * f D.b * f D.b
    simp only [map_add, map_sub, map_mul, map_ofNat]
  have hw₀ :
      f (quadraticTransverseAdjugateVector0 D
          (H 0 1) (H 0 2) (H 0 3)) =
        quadraticTransverseAdjugateVector0 C
          (Polynomial.derivative (b 0))
          (Polynomial.derivative (b 1))
          (Polynomial.derivative (b 2)) := by
    unfold quadraticTransverseAdjugateVector0
    simp only [map_add, map_sub, map_mul]
    rw [hv₀, hv₁, hv₂]
    rfl
  have hw₁ :
      f (quadraticTransverseAdjugateVector1 D
          (H 0 1) (H 0 2) (H 0 3)) =
        quadraticTransverseAdjugateVector1 C
          (Polynomial.derivative (b 0))
          (Polynomial.derivative (b 1))
          (Polynomial.derivative (b 2)) := by
    unfold quadraticTransverseAdjugateVector1
    simp only [map_add, map_sub, map_mul]
    rw [hv₀, hv₁, hv₂]
    rfl
  have hw₂ :
      f (quadraticTransverseAdjugateVector2 D
          (H 0 1) (H 0 2) (H 0 3)) =
        quadraticTransverseAdjugateVector2 C
          (Polynomial.derivative (b 0))
          (Polynomial.derivative (b 1))
          (Polynomial.derivative (b 2)) := by
    unfold quadraticTransverseAdjugateVector2
    simp only [map_add, map_sub, map_mul]
    rw [hv₀, hv₁, hv₂]
    rfl
  have hδ₀ :
      f (MvPolynomial.pderiv i.succ (H 0 1)) =
        Polynomial.derivative
          (quadraticSourceSectionHessian F (fun _ : Fin 3 => 0)
            i.succ (0 : Fin 3).succ) :=
    quadraticSource_axisMixedTransverseDerivative_eq_blockDerivative F i 0
  have hδ₁ :
      f (MvPolynomial.pderiv i.succ (H 0 2)) =
        Polynomial.derivative
          (quadraticSourceSectionHessian F (fun _ : Fin 3 => 0)
            i.succ (1 : Fin 3).succ) :=
    quadraticSource_axisMixedTransverseDerivative_eq_blockDerivative F i 1
  have hδ₂ :
      f (MvPolynomial.pderiv i.succ (H 0 3)) =
        Polynomial.derivative
          (quadraticSourceSectionHessian F (fun _ : Fin 3 => 0)
            i.succ (2 : Fin 3).succ) :=
    quadraticSource_axisMixedTransverseDerivative_eq_blockDerivative F i 2
  have hmap :
      f (MvPolynomial.pderiv i.succ (H 0 0)) *
          f D.determinantCore =
        (2 : Polynomial K) *
          (f (MvPolynomial.pderiv i.succ (H 0 1)) *
              f (quadraticTransverseAdjugateVector0 D
                (H 0 1) (H 0 2) (H 0 3)) +
            f (MvPolynomial.pderiv i.succ (H 0 2)) *
              f (quadraticTransverseAdjugateVector1 D
                (H 0 1) (H 0 2) (H 0 3)) +
            f (MvPolynomial.pderiv i.succ (H 0 3)) *
              f (quadraticTransverseAdjugateVector2 D
                (H 0 1) (H 0 2) (H 0 3))) := by
    simpa only [map_mul, map_add, map_ofNat] using
      congrArg f (quadraticSource_transverseSchurDerivative_equation
        F hbound hdet i)
  rw [hmapdet, hthree] at hmap
  simp only [mul_zero] at hmap
  have htwo : (2 : Polynomial K) ≠ 0 := by norm_num
  have hsum :
      f (MvPolynomial.pderiv i.succ (H 0 1)) *
          f (quadraticTransverseAdjugateVector0 D
            (H 0 1) (H 0 2) (H 0 3)) +
        f (MvPolynomial.pderiv i.succ (H 0 2)) *
          f (quadraticTransverseAdjugateVector1 D
            (H 0 1) (H 0 2) (H 0 3)) +
        f (MvPolynomial.pderiv i.succ (H 0 3)) *
          f (quadraticTransverseAdjugateVector2 D
            (H 0 1) (H 0 2) (H 0 3)) = 0 :=
    (mul_eq_zero.mp hmap.symm).resolve_left htwo
  simpa only [hδ₀, hδ₁, hδ₂, hw₀, hw₁, hw₂] using hsum

end
end HC4.Valuation
