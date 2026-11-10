import HC4.Valuation.QuadraticTransverseCapSourceAxisJetEndpoint
import Mathlib.Tactic

/-!
# Genuine source: mixed transverse derivative and axis Schur differential

For the actual four-variable source F, commute the third partials to
identify the transverse derivative of a longitudinal/transverse mixed
Hessian entry with the longitudinal derivative of the corresponding
transverse Hessian entry. Restricting to the marked axis gives the
DERIVATIVE of the genuine axis transverse block, not an invented C.

We also differentiate the genuine full-source Schur core in a transverse
direction under the proven transverse quadratic cap. The resulting
equation remains inside the actual source ring. The next lemma maps it
to K[x], where the axis transverse 3x3 determinant may vanish.
-/

namespace HC4.Valuation

noncomputable section
open HC4.Newton

variable {K : Type*} [Field K] [CharZero K]

/-- Exact three-partial commutation: d_yi H_(0,j) = d_x H_(i,j)
for the actual source Hessian. No transverse degree bound is needed. -/
theorem quadraticSource_mixedHessian_transverseDerivative_commute
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 3) :
    MvPolynomial.pderiv i.succ
        (HC4.Polynomial.hessian F 0 j.succ) =
      MvPolynomial.pderiv 0
        (HC4.Polynomial.hessian F i.succ j.succ) := by
  change
    MvPolynomial.pderiv i.succ
        (MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv 0 F)) =
      MvPolynomial.pderiv 0
        (MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv i.succ F))
  calc
    MvPolynomial.pderiv i.succ
        (MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv 0 F)) =
      MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv i.succ
          (MvPolynomial.pderiv 0 F)) :=
        MvPolynomial.pderiv_comm i.succ j.succ _
    _ = MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv 0
            (MvPolynomial.pderiv i.succ F)) := by
          rw [MvPolynomial.pderiv_comm i.succ 0 F]
    _ = MvPolynomial.pderiv 0
          (MvPolynomial.pderiv j.succ
            (MvPolynomial.pderiv i.succ F)) :=
        MvPolynomial.pderiv_comm j.succ 0 _

/-- The transverse derivative of an actual mixed Hessian entry,
restricted to the longitudinal axis, is the ordinary derivative of
the corresponding actual transverse Hessian polynomial on that axis. -/
theorem quadraticSource_axisMixedTransverseDerivative_eq_blockDerivative
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 3) :
    quadraticSourceSectionRingHom (K := K) (fun _ : Fin 3 => 0)
      (MvPolynomial.pderiv i.succ
        (HC4.Polynomial.hessian F 0 j.succ)) =
      Polynomial.derivative
        (quadraticSourceSectionHessian F (fun _ : Fin 3 => 0)
          i.succ j.succ) := by
  change
    longitudinalAxisRestriction
      (MvPolynomial.pderiv i.succ
        (HC4.Polynomial.hessian F 0 j.succ)) =
      Polynomial.derivative
        (longitudinalAxisRestriction
          (HC4.Polynomial.hessian F i.succ j.succ))
  rw [quadraticSource_mixedHessian_transverseDerivative_commute F i j]
  exact longitudinalAxisRestriction_pderiv_zero _

/-- Differentiate the exact source Hessian determinant-one identity in
a transverse direction. The quadratic cap makes every entry of the
transverse 3x3 block constant along that direction. -/
theorem quadraticSource_transverseSchurDerivative_equation
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (i : Fin 3) :
    let H := HC4.Polynomial.hessian F
    let C : GeneralThreeBlock (MvPolynomial (Fin 4) K) :=
      { a := H 1 1, b := H 1 2, c := H 1 3,
        d := H 2 2, e := H 2 3, f := H 3 3 }
    MvPolynomial.pderiv i.succ (H 0 0) * C.determinantCore =
      2 * (
        MvPolynomial.pderiv i.succ (H 0 1) *
          quadraticTransverseAdjugateVector0 C (H 0 1) (H 0 2) (H 0 3) +
        MvPolynomial.pderiv i.succ (H 0 2) *
          quadraticTransverseAdjugateVector1 C (H 0 1) (H 0 2) (H 0 3) +
        MvPolynomial.pderiv i.succ (H 0 3) *
          quadraticTransverseAdjugateVector2 C (H 0 1) (H 0 2) (H 0 3)) := by
  dsimp only
  let H := HC4.Polynomial.hessian F
  let C : GeneralThreeBlock (MvPolynomial (Fin 4) K) :=
    { a := H 1 1, b := H 1 2, c := H 1 3,
      d := H 2 2, e := H 2 3, f := H 3 3 }
  have ha : MvPolynomial.pderiv i.succ C.a = 0 :=
    transverseCapTwo_transverseHessian_pderiv_zero F hbound 0 0 i
  have hb : MvPolynomial.pderiv i.succ C.b = 0 :=
    transverseCapTwo_transverseHessian_pderiv_zero F hbound 0 1 i
  have hc : MvPolynomial.pderiv i.succ C.c = 0 :=
    transverseCapTwo_transverseHessian_pderiv_zero F hbound 0 2 i
  have hd : MvPolynomial.pderiv i.succ C.d = 0 :=
    transverseCapTwo_transverseHessian_pderiv_zero F hbound 1 1 i
  have he : MvPolynomial.pderiv i.succ C.e = 0 :=
    transverseCapTwo_transverseHessian_pderiv_zero F hbound 1 2 i
  have hf : MvPolynomial.pderiv i.succ C.f = 0 :=
    transverseCapTwo_transverseHessian_pderiv_zero F hbound 2 2 i
  have hunit :
      quadraticAxisFourBlockCore
        (H 0 0) (H 0 1) (H 0 2) (H 0 3)
        C.a C.b C.c C.d C.e C.f = 1 :=
    quadraticSource_fullHessian_schurCore_one F hdet
  have hder :=
    quadraticAxisFourBlockCore_transverse_pderiv_frozenBlock
      i (H 0 0) (H 0 1) (H 0 2) (H 0 3) C
      ha hb hc hd he hf
  have hzero :
      MvPolynomial.pderiv i.succ (H 0 0) * C.determinantCore -
        2 * (
          MvPolynomial.pderiv i.succ (H 0 1) *
            quadraticTransverseAdjugateVector0 C (H 0 1) (H 0 2) (H 0 3) +
          MvPolynomial.pderiv i.succ (H 0 2) *
            quadraticTransverseAdjugateVector1 C (H 0 1) (H 0 2) (H 0 3) +
          MvPolynomial.pderiv i.succ (H 0 3) *
            quadraticTransverseAdjugateVector2 C (H 0 1) (H 0 2) (H 0 3)) = 0 := by
    calc
      _ = MvPolynomial.pderiv i.succ
          (quadraticAxisFourBlockCore
            (H 0 0) (H 0 1) (H 0 2) (H 0 3)
            C.a C.b C.c C.d C.e C.f) := hder.symm
      _ = MvPolynomial.pderiv i.succ (1 : MvPolynomial (Fin 4) K) :=
        congrArg _ hunit
      _ = 0 := MvPolynomial.pderiv_one
  exact sub_eq_zero.mp hzero

end
end HC4.Valuation
