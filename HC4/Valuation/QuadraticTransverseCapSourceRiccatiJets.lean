import HC4.Valuation.QuadraticTransverseCapSourceSchurProfile
import Mathlib.Tactic

/-!
# Genuine source Hessian jets for the transverse quadratic Riccati equation

These statements are identities of the **original four-variable source**.
They introduce no quadratic normal-form replacement and require no
determinant or rank hypothesis.

The matrix Riccati identity in the rank-three quadratic branch comes
from twice differentiating the global determinant-one Schur equation
in the transverse directions, then restricting to the marked axis.

This file supplies the two foundational source-level facts:

* the global four-by-four Hessian is exactly a symmetric Schur block
  with determinant one, without restricting coordinates;
* the transverse second jet of its longitudinal H₀₀ entry, on the
  marked axis, equals the second longitudinal derivative Cᵢⱼ''(x)
  of the actual transverse Hessian matrix.

Remaining work: differentiate the global Schur equation twice,
use the source cap-two vanishing third transverse derivatives,
and collect the quadratic mixed-row terms into
  (det C) C'' = 2 C' adj(C) C'.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K]

/-- The exact global source Hessian, stored in the existing
symmetric 4x4 Schur block API. -/
noncomputable def quadraticTransverseCapSourceGlobalFourBlock
    (F : MvPolynomial (Fin 4) K) :
    GeneralFourBlock (MvPolynomial (Fin 4) K) :=
  GeneralFourBlock.ofSymmetricMatrix (HC4.Polynomial.hessian F)

/-- The global Hessian retains the symmetric-matrix data needed
for the Schur block constructor. -/
theorem quadraticTransverseCapSourceGlobalHessian_symmetric
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 4) :
    HC4.Polynomial.hessian F i j =
      HC4.Polynomial.hessian F j i := by
  change
    MvPolynomial.pderiv j (MvPolynomial.pderiv i F) =
      MvPolynomial.pderiv i (MvPolynomial.pderiv j F)
  exact (pderiv_comm_commRing i j F).symm

/-- The determinant-one identity is a literal polynomial equation
for the original GLOBAL four-block Hessian, rather than merely
for its longitudinal-axis or special-section evaluations. -/
theorem quadraticTransverseCapSourceGlobalFourBlock_unit
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    (quadraticTransverseCapSourceGlobalFourBlock F).determinantCore = 1 := by
  let H := quadraticTransverseCapSourceGlobalFourBlock F
  have hmatrix :
      H.matrix = HC4.Polynomial.hessian F :=
    GeneralFourBlock.matrix_ofSymmetricMatrix
      (HC4.Polynomial.hessian F)
      (quadraticTransverseCapSourceGlobalHessian_symmetric F)
  calc
    H.determinantCore = H.matrix.det :=
      (GeneralFourBlock.matrix_det H).symm
    _ = (HC4.Polynomial.hessian F).det := by rw [hmatrix]
    _ = HC4.Polynomial.hessianDeterminant F := rfl
    _ = 1 := hdet

/-- The real determinant-one source satisfies the full
nonlinear Schur determinant identity BEFORE taking a transverse
coefficient. This is the starting polynomial identity for Riccati. -/
theorem quadraticTransverseCapSourceGlobalSchur_unit
    (F : MvPolynomial (Fin 4) K)
    (hdet : HC4.Polynomial.hessianDeterminant F = 1) :
    let H := quadraticTransverseCapSourceGlobalFourBlock F
    quadraticAxisFourBlockCore H.a H.b H.p H.q
      H.d H.r H.s H.x H.y H.z = 1 := by
  dsimp only
  rw [quadraticAxisFourBlockCore_eq_generalFourBlock]
  exact quadraticTransverseCapSourceGlobalFourBlock_unit F hdet

/-- Transverse twice-differentiated H₀₀, restricted to the ORIGINAL
longitudinal source axis, equals the ordinary second derivative
of the transverse Hessian polynomial Cᵢⱼ(x).

This is the exact Hessian-jet coefficient that must multiply det C
in the rank-three Riccati equation. No cap-two hypothesis is needed:
it follows just from commutation of formal partial derivatives. -/
theorem quadraticTransverseCapSource_axisLongitudinal_secondTransverseJet
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 3) :
    longitudinalAxisRestrictionRingHom (K := K)
      (MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv i.succ
          (HC4.Polynomial.hessian F 0 0))) =
      Polynomial.derivative
        (Polynomial.derivative
          ((quadraticTransverseCapSourceAxisThreeBlock F).matrix i j)) := by
  rw [← quadraticTransverseCapSource_axisThreeBlock_entry F i j]
  change
    longitudinalAxisRestriction
      (MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv i.succ
          (MvPolynomial.pderiv (0 : Fin 4)
            (MvPolynomial.pderiv (0 : Fin 4) F)))) =
    Polynomial.derivative
      (Polynomial.derivative
        (longitudinalAxisRestriction
          (MvPolynomial.pderiv j.succ
            (MvPolynomial.pderiv i.succ F))))
  have hcomm :
      MvPolynomial.pderiv j.succ
        (MvPolynomial.pderiv i.succ
          (MvPolynomial.pderiv (0 : Fin 4)
            (MvPolynomial.pderiv (0 : Fin 4) F))) =
      MvPolynomial.pderiv (0 : Fin 4)
        (MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv j.succ
            (MvPolynomial.pderiv i.succ F))) := by
    calc
      MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv i.succ
            (MvPolynomial.pderiv (0 : Fin 4)
              (MvPolynomial.pderiv (0 : Fin 4) F))) =
        MvPolynomial.pderiv j.succ
          (MvPolynomial.pderiv (0 : Fin 4)
            (MvPolynomial.pderiv i.succ
              (MvPolynomial.pderiv (0 : Fin 4) F))) := by
                rw [pderiv_comm_commRing i.succ (0 : Fin 4)
                  (MvPolynomial.pderiv (0 : Fin 4) F)]
      _ = MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv j.succ
            (MvPolynomial.pderiv i.succ
              (MvPolynomial.pderiv (0 : Fin 4) F))) := by
                rw [pderiv_comm_commRing j.succ (0 : Fin 4)
                  (MvPolynomial.pderiv i.succ
                    (MvPolynomial.pderiv (0 : Fin 4) F))]
      _ = MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv j.succ
            (MvPolynomial.pderiv (0 : Fin 4)
              (MvPolynomial.pderiv i.succ F))) := by
                rw [pderiv_comm_commRing i.succ (0 : Fin 4) F]
      _ = MvPolynomial.pderiv (0 : Fin 4)
          (MvPolynomial.pderiv (0 : Fin 4)
            (MvPolynomial.pderiv j.succ
              (MvPolynomial.pderiv i.succ F))) := by
                rw [pderiv_comm_commRing j.succ (0 : Fin 4)
                  (MvPolynomial.pderiv i.succ F)]
  rw [hcomm, longitudinalAxisRestriction_pderiv_zero,
    longitudinalAxisRestriction_pderiv_zero]

end

end HC4.Valuation
