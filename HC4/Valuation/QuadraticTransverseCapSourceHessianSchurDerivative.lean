import HC4.Valuation.QuadraticTransverseCapSourceHessianSections
import Mathlib.Tactic

/-!
# Transverse derivatives of the ACTUAL four-variable determinant-one identity

This is a shorter alternative to expanding six opposite transverse
sections. The genuine Hessian determinant is an identity in the full
four-variable source ring. Differentiating in a transverse direction
is legitimate before restricting to the distinguished longitudinal axis.

When the transverse 3x3 block has zero transverse partial derivative
(the already-green quadratic-cap theorem), the Schur derivative is

  D(det Hess F) = (D u) det C - 2 (D v) dot adj(C) v.

The factor two is handled in characteristic zero, not by illicit
division in a general ring. The next adapter will evaluate at the marked
axis and identify D v with C' using mixed-partial commutation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton

variable {K : Type*} [Field K]

/-- A genuine source-level 1+3 determinant identity, without replacing
the source by a section, formal family or auxiliary normal form. -/
theorem quadraticSource_fullHessian_schurCore_one
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    let H := HC4.Polynomial.hessian F
    quadraticAxisFourBlockCore
      (H 0 0) (H 0 1) (H 0 2) (H 0 3)
      (H 1 1) (H 1 2) (H 1 3)
      (H 2 2) (H 2 3) (H 3 3) = 1 := by
  dsimp only
  let H := HC4.Polynomial.hessian F
  let B := GeneralFourBlock.ofSymmetricMatrix H
  have hsymm : ∀ i j : Fin 4, H i j = H j i := by
    intro i j
    change
      MvPolynomial.pderiv j (MvPolynomial.pderiv i F) =
        MvPolynomial.pderiv i (MvPolynomial.pderiv j F)
    exact (pderiv_comm_commRing i j F).symm
  have hdisplay : B.matrix = H :=
    GeneralFourBlock.matrix_ofSymmetricMatrix H hsymm
  have hcore :
      quadraticAxisFourBlockCore
        (H 0 0) (H 0 1) (H 0 2) (H 0 3)
        (H 1 1) (H 1 2) (H 1 3)
        (H 2 2) (H 2 3) (H 3 3) =
        B.determinantCore := by
    dsimp [B, GeneralFourBlock.ofSymmetricMatrix,
      quadraticAxisFourBlockCore, GeneralFourBlock.determinantCore]
    ring
  calc
    quadraticAxisFourBlockCore
        (H 0 0) (H 0 1) (H 0 2) (H 0 3)
        (H 1 1) (H 1 2) (H 1 3)
        (H 2 2) (H 2 3) (H 3 3) =
      B.determinantCore := hcore
    _ = B.matrix.det := (GeneralFourBlock.matrix_det B).symm
    _ = H.det := by rw [hdisplay]
    _ = 1 := by simpa [H, HC4.Polynomial.hessianDeterminant] using hdet

/-- Differentiate the 1+3 Schur core in a direction along which the
symmetric transverse block C is constant. This is a commutative-ring
polynomial identity with no inverse or principal pivot. -/
theorem quadraticAxisFourBlockCore_transverse_pderiv_frozenBlock
    (i : Fin 3)
    (u v₀ v₁ v₂ : MvPolynomial (Fin 4) K)
    (C : GeneralThreeBlock (MvPolynomial (Fin 4) K))
    (ha : MvPolynomial.pderiv i.succ C.a = 0)
    (hb : MvPolynomial.pderiv i.succ C.b = 0)
    (hc : MvPolynomial.pderiv i.succ C.c = 0)
    (hd : MvPolynomial.pderiv i.succ C.d = 0)
    (he : MvPolynomial.pderiv i.succ C.e = 0)
    (hf : MvPolynomial.pderiv i.succ C.f = 0) :
    MvPolynomial.pderiv i.succ
      (quadraticAxisFourBlockCore u v₀ v₁ v₂
        C.a C.b C.c C.d C.e C.f) =
      MvPolynomial.pderiv i.succ u * C.determinantCore -
        2 * (
          MvPolynomial.pderiv i.succ v₀ *
            quadraticTransverseAdjugateVector0 C v₀ v₁ v₂ +
          MvPolynomial.pderiv i.succ v₁ *
            quadraticTransverseAdjugateVector1 C v₀ v₁ v₂ +
          MvPolynomial.pderiv i.succ v₂ *
            quadraticTransverseAdjugateVector2 C v₀ v₁ v₂) := by
  unfold quadraticAxisFourBlockCore
    GeneralThreeBlock.determinantCore
    quadraticTransverseAdjugateVector0
    quadraticTransverseAdjugateVector1
    quadraticTransverseAdjugateVector2
  simp only [map_add, map_sub, map_neg, MvPolynomial.pderiv_mul,
    ha, hb, hc, hd, he, hf,
    mul_zero, zero_mul, add_zero, zero_add, sub_zero, zero_sub]
  ring

end
end HC4.Valuation
