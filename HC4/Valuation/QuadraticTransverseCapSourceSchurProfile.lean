import HC4.Valuation.QuadraticTransverseCapSourceMixedSections
import HC4.Valuation.QuadraticTransverseCapSevenSectionEndpoint
import Mathlib.Tactic

/-!
# Actual represented-source quadratic Schur section profile

The canonical source-axis three-block C(x) is the lower-right
3x3 submatrix of the actual source-axis four-block Hessian.
This follows from the existing symmetric matrix constructors and
their exact inverse formula.

Likewise the mixed source section row is the first row of the
actual four-block. By the transverse cap-two affine section theorem,

  H(0,i)(x,t e_j) = b_i'(x) + t * C_ij'(x).

These identities are in the univariate polynomial ring K[x],
with no assumed normal form or section profile constructor.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

variable {K : Type*} [Field K]

/-- The actual polynomial 3x3 transverse axis block is exactly the
transverse submatrix of the actual source Hessian restricted to x₀. -/
theorem quadraticTransverseCapSource_axisThreeBlock_entry
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 3) :
    longitudinalAxisRestrictionRingHom (K := K)
        (HC4.Polynomial.hessian F i.succ j.succ) =
      (quadraticTransverseCapSourceAxisThreeBlock F).matrix i j := by
  let H := quadraticTransverseCapSourceAxisFourBlock F
  have hfour :
      H.matrix =
        (HC4.Polynomial.hessian F).map
          (longitudinalAxisRestrictionRingHom (K := K)) := by
    exact GeneralFourBlock.matrix_ofSymmetricMatrix _
      (quadraticTransverseCapSourceAxisHessian_symmetric F)
  have hsub :
      (quadraticTransverseCapSourceAxisThreeBlock F).matrix i j =
        H.matrix i.succ j.succ := by
    fin_cases i <;> fin_cases j <;>
      simp [H, quadraticTransverseCapSourceAxisThreeBlock,
        GeneralThreeBlock.matrix, GeneralFourBlock.matrix]
  calc
    longitudinalAxisRestrictionRingHom (K := K)
        (HC4.Polynomial.hessian F i.succ j.succ) =
      ((HC4.Polynomial.hessian F).map
        (longitudinalAxisRestrictionRingHom (K := K)))
          i.succ j.succ := by rw [Matrix.map_apply]
    _ = H.matrix i.succ j.succ := by rw [← hfour]
    _ = (quadraticTransverseCapSourceAxisThreeBlock F).matrix i j :=
      hsub.symm

/-- The mixed part of an arbitrary actual four-block is the
three-component row in source indices 1,2,3. -/
def quadraticTransverseCapFourBlock_mixedRow
    (H : GeneralFourBlock (Polynomial K)) : Fin 3 → Polynomial K :=
  ![H.b, H.p, H.q]

/-- Each entry of the actual source-section mixed row is
exactly the corresponding restricted Hessian polynomial. -/
theorem quadraticTransverseCapSource_sectionMixedRow_entry
    (F : MvPolynomial (Fin 4) K)
    (y : Fin 3 → K)
    (i : Fin 3) :
    quadraticTransverseCapFourBlock_mixedRow
        (quadraticTransverseSourceSectionFourBlock F y) i =
      quadraticTransverseSourceSectionRingHom y
        (HC4.Polynomial.hessian F 0 i.succ) := by
  fin_cases i <;>
    simp [quadraticTransverseCapFourBlock_mixedRow,
      quadraticTransverseSourceSectionFourBlock,
      GeneralFourBlock.ofSymmetricMatrix, Matrix.map_apply]

/-- The exact mixed Schur row at y=t e_j in terms of the
ORIGINAL SOURCE'S univariate coefficient vector b(x) and
its univariate transverse Hessian C(x).

This is the final profile identification required for all
six opposite-section Schur equations in the rank-two branch. -/
theorem quadraticTransverseCap_two_sectionMixedRow_affine
    [CharZero K]
    (F : MvPolynomial (Fin 4) K)
    (hbound : HasReverseWeightBound topKernelMarkedAxisNatWeight 2 F)
    (i j : Fin 3)
    (t : K) :
    let b := quadraticTransverseCapSourceLinearCoefficients F
    let C := quadraticTransverseCapSourceAxisThreeBlock F
    quadraticTransverseCapFourBlock_mixedRow
        (quadraticTransverseSourceSectionFourBlock F
          (fun k : Fin 3 => if k = j then t else 0)) i =
      Polynomial.derivative (b i) +
        Polynomial.C t * Polynomial.derivative (C.matrix i j) := by
  dsimp only
  let b := quadraticTransverseCapSourceLinearCoefficients F
  let C := quadraticTransverseCapSourceAxisThreeBlock F
  calc
    quadraticTransverseCapFourBlock_mixedRow
        (quadraticTransverseSourceSectionFourBlock F
          (fun k : Fin 3 => if k = j then t else 0)) i =
      quadraticTransverseSourceSectionRingHom
        (fun k : Fin 3 => if k = j then t else 0)
        (HC4.Polynomial.hessian F 0 i.succ) :=
          quadraticTransverseCapSource_sectionMixedRow_entry F _ i
    _ = longitudinalAxisRestrictionRingHom (K := K)
          (HC4.Polynomial.hessian F 0 i.succ) +
        Polynomial.C t *
          Polynomial.derivative
            (longitudinalAxisRestrictionRingHom (K := K)
              (HC4.Polynomial.hessian F i.succ j.succ)) :=
          quadraticTransverseCap_two_mixedHessian_basisSection
            F hbound i j t
    _ = Polynomial.derivative (b i) +
        Polynomial.C t * Polynomial.derivative (C.matrix i j) := by
          rw [quadraticTransverseCapSource_axisThreeBlock_entry]
          rw [longitudinalAxisRestrictionRingHom_apply]
          exact congrArg (fun p : Polynomial K =>
            p + Polynomial.C t *
              Polynomial.derivative (C.matrix i j))
            (longitudinalAxisRestriction_hessian_zero_succ i F)

end

end HC4.Valuation
