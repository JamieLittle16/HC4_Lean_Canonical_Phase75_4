import HC4.Newton.FiniteSupportSingularBoundaryCarrierKernel
import Mathlib.Tactic

/-!
# First honest opening of the canonical codimension-two carrier kernel

The canonical A18.5.92 exposed vertex is obtained from a singular source `F`
by the finite chain

    F -> D0.face -> D1.face -> D2.face,

where `Dr` is the exact coordinate-maximal initial form in coordinate `r`.
For a codimension-two exposed vertex, the previous module proves that the final
stored carrier `D2.face` has a literal coordinate kernel in one of coordinates
`0,1,2`.

There are then only two possibilities:

* that same coordinate is already a kernel of the original singular source;
* or, moving along the three exact initial-form steps, there is a first child
  on which the kernel holds while its parent still breaks it.

This file retains that first opening together with the exact coordinate-max
weight, level, singularity, nonzeroness and source-support provenance.  No Rees
family or repair step is introduced yet.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

variable {K : Type*} [Field K] [CharZero K]

/-- One exact coordinate-maximal extraction at which a coordinate kernel first
appears. -/
structure CanonicalCoordinateMaxKernelOpeningData
    (F : MvPolynomial (Fin 4) K) where
  parent : MvPolynomial (Fin 4) K
  child : MvPolynomial (Fin 4) K
  extractionCoordinate : Fin 4
  extractionLevel : ℕ
  kernelCoordinate : Fin 4
  parent_hessian_zero : hessianDeterminant parent = 0
  child_hessian_zero : hessianDeterminant child = 0
  child_ne_zero : child ≠ 0
  child_eq_initialForm :
    child = initialForm
      (coordinateMaxWeight extractionCoordinate)
      (extractionLevel : ℤ) parent
  weight_bound :
    IsWeightLE
      (coordinateMaxWeight extractionCoordinate)
      (extractionLevel : ℤ) parent
  parent_support_subset_source : parent.support ⊆ F.support
  child_support_subset_source : child.support ⊆ F.support
  child_kernel : MvPolynomial.pderiv kernelCoordinate child = 0
  parent_kernel_ne : MvPolynomial.pderiv kernelCoordinate parent ≠ 0

/-- The canonical codimension-two exposed-vertex construction either already
finds a coordinate kernel on the original singular source, or retains the
first exact coordinate-max step at which that kernel appears. -/
inductive CanonicalCodimensionTwoKernelOutcome
    (F : MvPolynomial (Fin 4) K) : Type
  | topKernel
      (kernelCoordinate : Fin 4)
      (kernel_eq_zero : MvPolynomial.pderiv kernelCoordinate F = 0)
  | firstOpening
      (data : CanonicalCoordinateMaxKernelOpeningData F)

/-- **Finite first-opening theorem for the canonical A18.5.92 chain.** -/
noncomputable def exposedSingularNonlinearBoundaryVertex_codimensionTwoKernelOutcome
    (F : MvPolynomial (Fin 4) K)
    (hF : F ≠ 0)
    (hzero : hessianDeterminant F = 0)
    (hnonlinear : ∀ d ∈ F.support, 3 ≤ ordinaryDegree4 d)
    (hcodim : MvExponentOnCodimensionTwoBoundary
      (exposedSingularNonlinearBoundaryVertex F hF hzero hnonlinear).exponent) :
    CanonicalCodimensionTwoKernelOutcome F := by
  let D0 := coordinateMaxInitialData F hF (0 : Fin 4)
  have h0zero : hessianDeterminant D0.face = 0 := D0.hessian_zero hzero
  let D1 := coordinateMaxInitialData D0.face D0.face_ne_zero (1 : Fin 4)
  have h1zero : hessianDeterminant D1.face = 0 := D1.hessian_zero h0zero
  let D2 := coordinateMaxInitialData D1.face D1.face_ne_zero (2 : Fin 4)
  have h2zero : hessianDeterminant D2.face = 0 := D2.hessian_zero h1zero

  rcases
      exposedSingularNonlinearBoundaryVertex_carrier_has_coordinateKernel_of_codimensionTwo
        F hF hzero hnonlinear hcodim with ⟨i, hkernel⟩
  let k : Fin 4 := Fin.castSucc i

  have hD2kernel : MvPolynomial.pderiv k D2.face = 0 := by
    simpa [k] using hkernel

  by_cases hFkernel : MvPolynomial.pderiv k F = 0
  · exact .topKernel k hFkernel
  · by_cases hD0kernel : MvPolynomial.pderiv k D0.face = 0
    · exact .firstOpening {
        parent := F
        child := D0.face
        extractionCoordinate := (0 : Fin 4)
        extractionLevel := D0.level
        kernelCoordinate := k
        parent_hessian_zero := hzero
        child_hessian_zero := h0zero
        child_ne_zero := D0.face_ne_zero
        child_eq_initialForm := D0.face_eq
        weight_bound := D0.weight_bound
        parent_support_subset_source := by intro d hd; exact hd
        child_support_subset_source := D0.support_subset
        child_kernel := hD0kernel
        parent_kernel_ne := hFkernel
      }
    · by_cases hD1kernel : MvPolynomial.pderiv k D1.face = 0
      · exact .firstOpening {
          parent := D0.face
          child := D1.face
          extractionCoordinate := (1 : Fin 4)
          extractionLevel := D1.level
          kernelCoordinate := k
          parent_hessian_zero := h0zero
          child_hessian_zero := h1zero
          child_ne_zero := D1.face_ne_zero
          child_eq_initialForm := D1.face_eq
          weight_bound := D1.weight_bound
          parent_support_subset_source := D0.support_subset
          child_support_subset_source := fun d hd => D0.support_subset (D1.support_subset hd)
          child_kernel := hD1kernel
          parent_kernel_ne := hD0kernel
        }
      · exact .firstOpening {
          parent := D1.face
          child := D2.face
          extractionCoordinate := (2 : Fin 4)
          extractionLevel := D2.level
          kernelCoordinate := k
          parent_hessian_zero := h1zero
          child_hessian_zero := h2zero
          child_ne_zero := D2.face_ne_zero
          child_eq_initialForm := D2.face_eq
          weight_bound := D2.weight_bound
          parent_support_subset_source := fun d hd =>
            D0.support_subset (D1.support_subset hd)
          child_support_subset_source := fun d hd =>
            D0.support_subset (D1.support_subset (D2.support_subset hd))
          child_kernel := hD2kernel
          parent_kernel_ne := hD1kernel
        }

end

end HC4.Newton
