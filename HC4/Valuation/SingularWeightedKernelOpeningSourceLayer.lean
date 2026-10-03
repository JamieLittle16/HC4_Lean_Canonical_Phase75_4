import HC4.Valuation.SingularWeightedKernelOpening
import Mathlib.Tactic

/-!
# Source-layer form of a generic singular weighted kernel opening

The active-three branch of `SingularWeightedKernelOpeningData.rankFrontier`
produces a principal Hessian minor at the first kernel-row breaking coefficient.
That is a statement about one parameter layer of the honest reverse-Rees
family, not about a principal minor of the whole parent polynomial.

This file performs exactly the source-honest conversion which is valid:
the nonzero breaking layer is identified with the corresponding exact weighted
initial form of the parent.  No cross-layer noncancellation is assumed.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K]

namespace SingularWeightedKernelOpeningData

variable {parent : MvPolynomial (Fin 4) K}
variable (D : SingularWeightedKernelOpeningData parent)

/-- The active-three first break as an exact weighted source component of the
singular parent.  The `which` index records which one of the three active
coordinates forms the nonzero principal minor with the kernel coordinate. -/
structure ExactParentWeightLayerMinorAtFirstBreak : Type u where
  order : ℕ
  order_pos : 0 < order
  order_le_level : order ≤ D.level
  which : Fin 3
  exactLayer :
    familyParameterLayer D.reverseReesFamily order =
      initialForm
        (fun i => (D.weight i : ℤ))
        ((D.level - order : ℕ) : ℤ)
        parent
  minor_ne_zero :
    hessianPrincipalMinor
        (initialForm
          (fun i => (D.weight i : ℤ))
          ((D.level - order : ℕ) : ℤ)
          parent)
        (kernelLastPerm D.kernelCoordinate which.castSucc)
        D.kernelCoordinate ≠ 0

private theorem hessianPrincipalMinor_eq_square
    (F : MvPolynomial (Fin 4) K)
    (i j : Fin 4) :
    hessianPrincipalMinor F i j =
      hessian F i i * hessian F j j -
        hessian F i j * hessian F i j := by
  have hsym : hessian F j i = hessian F i j := by
    change
      MvPolynomial.pderiv i (MvPolynomial.pderiv j F) =
        MvPolynomial.pderiv j (MvPolynomial.pderiv i F)
    exact MvPolynomial.pderiv_comm i j F
  unfold hessianPrincipalMinor
  rw [hsym]

private theorem layerMinor0_eq
    (j : ℕ) :
    let B := kernelLastFamilyHessianFourBlock
      D.reverseReesFamily D.kernelCoordinate
    B.a.coeff j * B.z.coeff j - B.q.coeff j * B.q.coeff j =
      hessianPrincipalMinor
        (familyParameterLayer D.reverseReesFamily j)
        (kernelLastPerm D.kernelCoordinate 0)
        D.kernelCoordinate := by
  dsimp only
  unfold kernelLastFamilyHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply, parameterFirstHessian_coeff,
    kernelLastPerm_last]
  rw [hessianPrincipalMinor_eq_square]

private theorem layerMinor1_eq
    (j : ℕ) :
    let B := kernelLastFamilyHessianFourBlock
      D.reverseReesFamily D.kernelCoordinate
    B.d.coeff j * B.z.coeff j - B.s.coeff j * B.s.coeff j =
      hessianPrincipalMinor
        (familyParameterLayer D.reverseReesFamily j)
        (kernelLastPerm D.kernelCoordinate 1)
        D.kernelCoordinate := by
  dsimp only
  unfold kernelLastFamilyHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply, parameterFirstHessian_coeff,
    kernelLastPerm_last]
  rw [hessianPrincipalMinor_eq_square]

private theorem layerMinor2_eq
    (j : ℕ) :
    let B := kernelLastFamilyHessianFourBlock
      D.reverseReesFamily D.kernelCoordinate
    B.x.coeff j * B.z.coeff j - B.y.coeff j * B.y.coeff j =
      hessianPrincipalMinor
        (familyParameterLayer D.reverseReesFamily j)
        (kernelLastPerm D.kernelCoordinate 2)
        D.kernelCoordinate := by
  dsimp only
  unfold kernelLastFamilyHessianFourBlock GeneralFourBlock.ofSymmetricMatrix
    kernelLastParameterFirstHessian
  simp only [Matrix.submatrix_apply, parameterFirstHessian_coeff,
    kernelLastPerm_last]
  rw [hessianPrincipalMinor_eq_square]

/-- Convert the nondegenerate first-break coefficient minor into a literal
principal minor on one exact weighted component of the parent. -/
theorem exactParentWeightLayerMinor_of_activeThree
    (active_ne_zero :
      let B := kernelLastFamilyHessianFourBlock
        D.reverseReesFamily D.kernelCoordinate
      (firstKernelBreakActiveThreeDet B).coeff 0 ≠ 0)
    (firstLayerMinor :
      let B := kernelLastFamilyHessianFourBlock
        D.reverseReesFamily D.kernelCoordinate
      let hrow := D.kernelLastBlock_kernelRow_ne_zero
      let hzero := D.kernelLastBlock_kernelRow_coeff_zero
      let E := singularFirstKernelBreakData_of_kernelRow B hrow
        hzero.1 hzero.2.1 hzero.2.2.1 hzero.2.2.2
        active_ne_zero
        (kernelLastFamilyHessianFourBlock_determinantCore_eq_zero
          D.reverseReesFamily D.kernelCoordinate
          D.reverseReesFamily_hessianDeterminant_eq_zero)
      (E.block.a.coeff E.order * E.block.z.coeff E.order -
          E.block.q.coeff E.order * E.block.q.coeff E.order ≠ 0) ∨
      (E.block.d.coeff E.order * E.block.z.coeff E.order -
          E.block.s.coeff E.order * E.block.s.coeff E.order ≠ 0) ∨
      (E.block.x.coeff E.order * E.block.z.coeff E.order -
          E.block.y.coeff E.order * E.block.y.coeff E.order ≠ 0)) :
    Nonempty D.ExactParentWeightLayerMinorAtFirstBreak := by
  let B := kernelLastFamilyHessianFourBlock
    D.reverseReesFamily D.kernelCoordinate
  let hrow := D.kernelLastBlock_kernelRow_ne_zero
  let hzero := D.kernelLastBlock_kernelRow_coeff_zero
  let E := singularFirstKernelBreakData_of_kernelRow B hrow
    hzero.1 hzero.2.1 hzero.2.2.1 hzero.2.2.2
    active_ne_zero
    (kernelLastFamilyHessianFourBlock_determinantCore_eq_zero
      D.reverseReesFamily D.kernelCoordinate
      D.reverseReesFamily_hessianDeterminant_eq_zero)
  let j := E.order
  let L := familyParameterLayer D.reverseReesFamily j

  have hminor :
      hessianPrincipalMinor L
            (kernelLastPerm D.kernelCoordinate 0) D.kernelCoordinate ≠ 0 ∨
        hessianPrincipalMinor L
            (kernelLastPerm D.kernelCoordinate 1) D.kernelCoordinate ≠ 0 ∨
        hessianPrincipalMinor L
            (kernelLastPerm D.kernelCoordinate 2) D.kernelCoordinate ≠ 0 := by
    change
      B.a.coeff j * B.z.coeff j - B.q.coeff j * B.q.coeff j ≠ 0 ∨
        B.d.coeff j * B.z.coeff j - B.s.coeff j * B.s.coeff j ≠ 0 ∨
        B.x.coeff j * B.z.coeff j - B.y.coeff j * B.y.coeff j ≠ 0 at firstLayerMinor
    rcases firstLayerMinor with h0 | h1 | h2
    · left
      rw [← D.layerMinor0_eq j]
      exact h0
    · right
      left
      rw [← D.layerMinor1_eq j]
      exact h1
    · right
      right
      rw [← D.layerMinor2_eq j]
      exact h2

  have hLne : L ≠ 0 := by
    intro hzeroL
    rcases hminor with h0 | h1 | h2
    · apply h0
      rw [hzeroL]
      simp [hessianPrincipalMinor, hessian_apply]
    · apply h1
      rw [hzeroL]
      simp [hessianPrincipalMinor, hessian_apply]
    · apply h2
      rw [hzeroL]
      simp [hessianPrincipalMinor, hessian_apply]

  have hexact :=
    reverseWeightedReesFamily_parameterLayer_eq_initialForm_of_ne_zero
      D.weight D.level j parent D.weight_bound
      (by simpa [L, SingularWeightedKernelOpeningData.reverseReesFamily] using hLne)
  rcases hexact with ⟨hjle, hexact⟩
  have hexact' :
      L =
        initialForm
          (fun i => (D.weight i : ℤ))
          ((D.level - j : ℕ) : ℤ)
          parent := by
    simpa [L, SingularWeightedKernelOpeningData.reverseReesFamily] using hexact

  have hjpos : 0 < j := by
    dsimp [j, E]
    exact
      (singularFirstKernelBreakData_of_kernelRow B hrow
        hzero.1 hzero.2.1 hzero.2.2.1 hzero.2.2.2
        active_ne_zero
        (kernelLastFamilyHessianFourBlock_determinantCore_eq_zero
          D.reverseReesFamily D.kernelCoordinate
          D.reverseReesFamily_hessianDeterminant_eq_zero)).order_pos

  rcases hminor with h0 | h1 | h2
  · exact ⟨{
      order := j
      order_pos := hjpos
      order_le_level := hjle
      which := 0
      exactLayer := hexact'
      minor_ne_zero := by
        rw [← hexact']
        simpa using h0
    }⟩
  · exact ⟨{
      order := j
      order_pos := hjpos
      order_le_level := hjle
      which := 1
      exactLayer := hexact'
      minor_ne_zero := by
        rw [← hexact']
        simpa using h1
    }⟩
  · exact ⟨{
      order := j
      order_pos := hjpos
      order_le_level := hjle
      which := 2
      exactLayer := hexact'
      minor_ne_zero := by
        rw [← hexact']
        simpa using h2
    }⟩

/-- Assembly-facing refinement of the generic rank frontier.  The
nondegenerate branch is now a source-weight-component event; the degenerate
complementary-three-by-three equation is retained literally for the next
finite rank split. -/
inductive SourceLayerFrontier : Type (u + 1)
  | exactParentLayer
      (data : D.ExactParentWeightLayerMinorAtFirstBreak)
  | activeDegenerate
      (active_eq_zero :
        let B := kernelLastFamilyHessianFourBlock
          D.reverseReesFamily D.kernelCoordinate
        (firstKernelBreakActiveThreeDet B).coeff 0 = 0)

/-- No first-break information is lost in passing from the generic rank
frontier to the source-layer frontier. -/
theorem sourceLayerFrontier_nonempty :
    Nonempty D.SourceLayerFrontier := by
  cases D.rankFrontier with
  | activeThree hactive hminor =>
      rcases D.exactParentWeightLayerMinor_of_activeThree hactive hminor with
        ⟨L⟩
      exact ⟨.exactParentLayer L⟩
  | activeDegenerate hactive =>
      exact ⟨.activeDegenerate hactive⟩

/-- Canonical source-layer output of one generic singular weighted opening. -/
noncomputable def sourceLayerFrontier : D.SourceLayerFrontier :=
  Classical.choice D.sourceLayerFrontier_nonempty

end SingularWeightedKernelOpeningData

end

end HC4.Valuation
