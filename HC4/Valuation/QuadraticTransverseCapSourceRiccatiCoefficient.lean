import HC4.Valuation.QuadraticTransverseCapSchurSecondDerivative
import HC4.Valuation.QuadraticTransverseCapSourceHessianFlat
import Mathlib.Tactic

/-!
# The *actual* quadratic-cap source forces its Riccati coefficient

No abstract Hessian, assumed Schur equation, added source normal form,
or independently supplied derivative identities appear in the theorem
statement.

The original determinant-one polynomial F and its source-wide
transverse degree cap two force a division-free matrix Riccati
coefficient: det(C) times the longitudinal double derivative of
the transverse Hessian equals twice the adjugate contraction of
its two actual mixed-Hessian transverse derivatives.

All source derivatives and the exact global Schur determinant
are supplied by previously compiled source lemmas. This is
the obstruction previously missing at the source-to-Riccati seam.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K]

set_option maxHeartbeats 3000000

/-- For the ORIGINAL F of transverse degree <= 2 and determinant
Hessian one, the quadratic Schur coefficient of its true full Hessian
vanishes. The conclusion is a global polynomial identity in all four
source variables, not a section equation or an endpoint assumption.

Restricting this identity to the longitudinal axis gives
  det(C) * C'' = 2 C' adj(C) C'
for the actual source transverse Hessian matrix C(x). -/
theorem quadraticTransverseCapSource_globalRiccatiCoefficient
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1)
    (i j : Fin 3) :
    let H := quadraticTransverseCapSourceGlobalFourBlock F
    let C : GeneralThreeBlock (MvPolynomial (Fin 4) K) :=
      { a := H.d, b := H.r, c := H.s,
        d := H.x, e := H.y, f := H.z }
    MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv i.succ H.a) *
        C.determinantCore =
      2 * (
        MvPolynomial.pderiv i.succ H.b *
          quadraticTransverseAdjugateVector0 C
            (MvPolynomial.pderiv j.succ H.b)
            (MvPolynomial.pderiv j.succ H.p)
            (MvPolynomial.pderiv j.succ H.q) +
        MvPolynomial.pderiv i.succ H.p *
          quadraticTransverseAdjugateVector1 C
            (MvPolynomial.pderiv j.succ H.b)
            (MvPolynomial.pderiv j.succ H.p)
            (MvPolynomial.pderiv j.succ H.q) +
        MvPolynomial.pderiv i.succ H.q *
          quadraticTransverseAdjugateVector2 C
            (MvPolynomial.pderiv j.succ H.b)
            (MvPolynomial.pderiv j.succ H.p)
            (MvPolynomial.pderiv j.succ H.q)) := by
  classical
  let H := quadraticTransverseCapSourceGlobalFourBlock F
  let C : GeneralThreeBlock (MvPolynomial (Fin 4) K) :=
    { a := H.d, b := H.r, c := H.s,
      d := H.x, e := H.y, f := H.z }
  have hflat (t s l : Fin 3) :
      MvPolynomial.pderiv t.succ
        (HC4.Polynomial.hessian F s.succ l.succ) = 0 := by
    change MvPolynomial.pderiv t.succ
      (MvPolynomial.pderiv l.succ
        (MvPolynomial.pderiv s.succ F)) = 0
    exact quadraticTransverseCap_two_tripleTransversePderiv_zero
      F hbound s l t
  have hflatC (t : Fin 3) :
      MvPolynomial.pderiv t.succ C.a = 0 ∧
      MvPolynomial.pderiv t.succ C.b = 0 ∧
      MvPolynomial.pderiv t.succ C.c = 0 ∧
      MvPolynomial.pderiv t.succ C.d = 0 ∧
      MvPolynomial.pderiv t.succ C.e = 0 ∧
      MvPolynomial.pderiv t.succ C.f = 0 := by
    change
      MvPolynomial.pderiv t.succ
          (HC4.Polynomial.hessian F 1 1) = 0 ∧
      MvPolynomial.pderiv t.succ
          (HC4.Polynomial.hessian F 1 2) = 0 ∧
      MvPolynomial.pderiv t.succ
          (HC4.Polynomial.hessian F 1 3) = 0 ∧
      MvPolynomial.pderiv t.succ
          (HC4.Polynomial.hessian F 2 2) = 0 ∧
      MvPolynomial.pderiv t.succ
          (HC4.Polynomial.hessian F 2 3) = 0 ∧
      MvPolynomial.pderiv t.succ
          (HC4.Polynomial.hessian F 3 3) = 0
    exact ⟨hflat t 0 0, hflat t 0 1, hflat t 0 2,
      hflat t 1 1, hflat t 1 2, hflat t 2 2⟩
  have hmix (t s k : Fin 3) :
      MvPolynomial.pderiv t.succ
        (MvPolynomial.pderiv s.succ
          (HC4.Polynomial.hessian F 0 k.succ)) = 0 := by
    change MvPolynomial.pderiv t.succ
      (MvPolynomial.pderiv s.succ
        (MvPolynomial.pderiv k.succ
          (MvPolynomial.pderiv 0 F))) = 0
    calc
      MvPolynomial.pderiv t.succ
          (MvPolynomial.pderiv s.succ
            (MvPolynomial.pderiv k.succ
              (MvPolynomial.pderiv 0 F))) =
        MvPolynomial.pderiv 0
          (MvPolynomial.pderiv t.succ
            (MvPolynomial.pderiv s.succ
              (MvPolynomial.pderiv k.succ F))) := by
          rw [pderiv_comm_commRing k.succ (0 : Fin 4) F]
          rw [pderiv_comm_commRing s.succ (0 : Fin 4)
            (MvPolynomial.pderiv k.succ F)]
          rw [pderiv_comm_commRing t.succ (0 : Fin 4)
            (MvPolynomial.pderiv s.succ
              (MvPolynomial.pderiv k.succ F))]
      _ = 0 := by
        rw [quadraticTransverseCap_two_tripleTransversePderiv_zero
          F hbound k s t]
        simp
  have hmix0 :
      MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv i.succ H.b) = 0 := by
    change MvPolynomial.pderiv j.succ
      (MvPolynomial.pderiv i.succ
        (HC4.Polynomial.hessian F 0 1)) = 0
    exact hmix j i 0
  have hmix1 :
      MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv i.succ H.p) = 0 := by
    change MvPolynomial.pderiv j.succ
      (MvPolynomial.pderiv i.succ
        (HC4.Polynomial.hessian F 0 2)) = 0
    exact hmix j i 1
  have hmix2 :
      MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv i.succ H.q) = 0 := by
    change MvPolynomial.pderiv j.succ
      (MvPolynomial.pderiv i.succ
        (HC4.Polynomial.hessian F 0 3)) = 0
    exact hmix j i 2
  have hcore :
      quadraticAxisFourBlockCore H.a H.b H.p H.q
        C.a C.b C.c C.d C.e C.f = 1 := by
    exact quadraticTransverseCapSourceGlobalSchur_unit F hdet
  have hsecond :=
    quadraticTransverse_schur_secondDerivative
      (MvPolynomial.pderiv i.succ)
      (MvPolynomial.pderiv j.succ)
      H.a H.b H.p H.q C
      (hflatC i) (hflatC j)
      hmix0 hmix1 hmix2
  rw [hcore] at hsecond
  simp only [map_one] at hsecond
  exact sub_eq_zero.mp hsecond.symm

end

end HC4.Valuation
