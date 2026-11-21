import HC4.Valuation.QuadraticTransverseCapAffineSection
import Mathlib.Tactic

/-!
# Actual quadratic-cap mixed Hessian at transverse basis sections

Let F be the *represented* four-variable source, with transverse
degree at most two. The mixed Hessian H(0,i) has vanishing
second derivatives in every transverse coordinate. This follows
from the already-proved third-transverse-derivative identity and
commutation with the longitudinal derivative.

Its value on y=t e_j is therefore exactly

  H(0,i)(x,t e_j) =
    H(0,i)(x,0) + t * d/dx (H(i,j)(x,0)).

This is the source-honest affine Schur mixed-column formula.
No quadratic normal form, source replacement, or extra endpoint
producer is assumed.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K]

/-- Commutation of the longitudinal derivative with both
transverse Hessian derivatives, restricted to the real source axis. -/
theorem quadraticTransverseSource_axisMixedTransverse_derivative
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 3) :
    longitudinalAxisRestrictionRingHom (K := K)
        (MvPolynomial.pderiv j.succ
          (HC4.Polynomial.hessian F 0 i.succ)) =
      Polynomial.derivative
        (longitudinalAxisRestrictionRingHom (K := K)
          (HC4.Polynomial.hessian F i.succ j.succ)) := by
  have hcomm :
      MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv i.succ
            (MvPolynomial.pderiv (0 : Fin 4) F)) =
        MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv j.succ
            (MvPolynomial.pderiv i.succ F)) := by
    calc
      MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv i.succ
            (MvPolynomial.pderiv (0 : Fin 4) F)) =
        MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv (0 : Fin 4)
            (MvPolynomial.pderiv i.succ F)) := by
              rw [pderiv_comm_commRing i.succ (0 : Fin 4) F]
      _ = MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv j.succ
            (MvPolynomial.pderiv i.succ F)) := by
              rw [pderiv_comm_commRing j.succ (0 : Fin 4)
                (MvPolynomial.pderiv i.succ F)]
  change longitudinalAxisRestriction
      (MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv i.succ
          (MvPolynomial.pderiv (0 : Fin 4) F))) =
    (longitudinalAxisRestriction
      (MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv i.succ F))).derivative
  calc
    longitudinalAxisRestriction
        (MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv i.succ
            (MvPolynomial.pderiv (0 : Fin 4) F))) =
      longitudinalAxisRestriction
        (MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv j.succ
            (MvPolynomial.pderiv i.succ F))) := by
              rw [hcomm]
    _ = (longitudinalAxisRestriction
        (MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv i.succ F))).derivative :=
      longitudinalAxisRestriction_pderiv_zero _

/-- Each actual mixed Hessian H(0,i) is affine in every one
transverse coordinate when the whole source has transverse cap two. -/
theorem quadraticTransverseCap_two_mixedHessian_secondTransverse_zero
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (i j : Fin 3) :
    MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv j.succ
          (HC4.Polynomial.hessian F 0 i.succ)) = 0 := by
  have htriple :=
    quadraticTransverseCap_two_tripleTransversePderiv_zero
      F hbound i j j
  change
    MvPolynomial.pderiv j.succ
      (MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv i.succ
          (MvPolynomial.pderiv (0 : Fin 4) F))) = 0
  calc
    MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv i.succ
            (MvPolynomial.pderiv (0 : Fin 4) F))) =
      MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv (0 : Fin 4)
            (MvPolynomial.pderiv i.succ F))) := by
              rw [pderiv_comm_commRing i.succ (0 : Fin 4) F]
    _ = MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv j.succ
            (MvPolynomial.pderiv i.succ F))) := by
              rw [pderiv_comm_commRing j.succ (0 : Fin 4)
                (MvPolynomial.pderiv i.succ F)]
    _ = MvPolynomial.pderiv (0 : Fin 4)
        (MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv j.succ
            (MvPolynomial.pderiv i.succ F))) := by
              rw [pderiv_comm_commRing j.succ (0 : Fin 4)
                (MvPolynomial.pderiv j.succ
                  (MvPolynomial.pderiv i.succ F))]
    _ = 0 := by rw [htriple]; simp

/-- The exact mixed Hessian source-section identity needed
for the singular rank-two Schur endpoint.

Its right side contains *actual* represented-source axis
Hessian entries and their longitudinal polynomial derivatives.
There is no assumed affine Hessian profile. -/
theorem quadraticTransverseCap_two_mixedHessian_basisSection
    [CharZero K]
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (i j : Fin 3)
    (t : K) :
    quadraticTransverseSourceSectionRingHom
        (fun k : Fin 3 => if k = j then t else 0)
        (HC4.Polynomial.hessian F 0 i.succ) =
      longitudinalAxisRestrictionRingHom (K := K)
        (HC4.Polynomial.hessian F 0 i.succ) +
        Polynomial.C t *
          Polynomial.derivative
            (longitudinalAxisRestrictionRingHom (K := K)
              (HC4.Polynomial.hessian F i.succ j.succ)) := by
  calc
    quadraticTransverseSourceSectionRingHom
        (fun k : Fin 3 => if k = j then t else 0)
        (HC4.Polynomial.hessian F 0 i.succ) =
      longitudinalAxisRestrictionRingHom (K := K)
        (HC4.Polynomial.hessian F 0 i.succ) +
        Polynomial.C t *
          longitudinalAxisRestrictionRingHom (K := K)
            (MvPolynomial.pderiv j.succ
              (HC4.Polynomial.hessian F 0 i.succ)) :=
                quadraticTransverseSource_affineBasisSection
                  (HC4.Polynomial.hessian F 0 i.succ) j
                  (quadraticTransverseCap_two_mixedHessian_secondTransverse_zero
                    F hbound i j) t
    _ = longitudinalAxisRestrictionRingHom (K := K)
          (HC4.Polynomial.hessian F 0 i.succ) +
        Polynomial.C t *
          Polynomial.derivative
            (longitudinalAxisRestrictionRingHom (K := K)
              (HC4.Polynomial.hessian F i.succ j.succ)) := by
                rw [quadraticTransverseSource_axisMixedTransverse_derivative]

end

end HC4.Valuation
