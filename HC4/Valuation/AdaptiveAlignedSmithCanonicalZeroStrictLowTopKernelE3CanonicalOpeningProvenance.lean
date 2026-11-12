import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowTopKernelE3CanonicalOpeningChainMinorLift
import Mathlib.Tactic

/-!
# Exact provenance for the canonical codimension-two first opening

The original canonical singular-boundary selector constructs the first
coordinate-kernel opening along three explicit coordinate-max initial forms,
but its general opening record retains only support containment.  The latter
does not suffice to transport nonlinear Hessian minors to the source.

Here we retain the *actual chain identity* for the same canonical choice:
either F itself has a coordinate kernel, or the opening child is exactly one
of the three canonical faces F₀, F₁, F₂.  This enables the already-verified
arbitrary-minor three-step transport, without assuming an undocumented
identity for arbitrary opening records.
-/

namespace HC4.Valuation

noncomputable section
open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- The constructive codimension-two kernel selector with its original
three-face provenance restored.  The opening is derived from the actual
canonical coordinate-max chain rather than from support inclusion. -/
theorem canonicalCodimensionTwoKernel_or_firstOpening_withProvenance
    (F : MvPolynomial (Fin 4) K)
    (hF : F ≠ 0)
    (hzero : HC4.Polynomial.hessianDeterminant F = 0)
    (hnonlinear :
      ∀ d ∈ F.support, 3 ≤ HC4.Polynomial.ordinaryDegree4 d)
    (hcodim :
      MvExponentOnCodimensionTwoBoundary
        (exposedSingularNonlinearBoundaryVertex
          F hF hzero hnonlinear).exponent) :
    (∃ k : Fin 4, MvPolynomial.pderiv k F = 0) ∨
      (∃ O : CanonicalCoordinateMaxKernelOpeningData F,
        let D0 := coordinateMaxInitialData F hF (0 : Fin 4)
        let D1 := coordinateMaxInitialData
          D0.face D0.face_ne_zero (1 : Fin 4)
        let D2 := coordinateMaxInitialData
          D1.face D1.face_ne_zero (2 : Fin 4)
        O.child = D0.face ∨ O.child = D1.face ∨ O.child = D2.face) := by
  let D0 := coordinateMaxInitialData F hF (0 : Fin 4)
  have h0zero : HC4.Polynomial.hessianDeterminant D0.face = 0 :=
    D0.hessian_zero hzero
  let D1 := coordinateMaxInitialData D0.face D0.face_ne_zero (1 : Fin 4)
  have h1zero : HC4.Polynomial.hessianDeterminant D1.face = 0 :=
    D1.hessian_zero h0zero
  let D2 := coordinateMaxInitialData D1.face D1.face_ne_zero (2 : Fin 4)
  have h2zero : HC4.Polynomial.hessianDeterminant D2.face = 0 :=
    D2.hessian_zero h1zero

  let hex :=
    exposedSingularNonlinearBoundaryVertex_carrier_has_coordinateKernel_of_codimensionTwo
      F hF hzero hnonlinear hcodim
  let i := Classical.choose hex
  have hkernel := Classical.choose_spec hex
  let k : Fin 4 := Fin.castSucc i
  have hD2kernel : MvPolynomial.pderiv k D2.face = 0 := by
    simpa [k] using hkernel

  by_cases hFkernel : MvPolynomial.pderiv k F = 0
  · exact Or.inl ⟨k, hFkernel⟩
  · right
    by_cases hD0kernel : MvPolynomial.pderiv k D0.face = 0
    · refine ⟨{
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
      }, ?_⟩
      exact Or.inl rfl
    · by_cases hD1kernel : MvPolynomial.pderiv k D1.face = 0
      · refine ⟨{
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
          child_support_subset_source :=
            fun d hd => D0.support_subset (D1.support_subset hd)
          child_kernel := hD1kernel
          parent_kernel_ne := hD0kernel
        }, ?_⟩
        exact Or.inr (Or.inl rfl)
      · refine ⟨{
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
          parent_support_subset_source :=
            fun d hd => D0.support_subset (D1.support_subset hd)
          child_support_subset_source :=
            fun d hd => D0.support_subset (D1.support_subset (D2.support_subset hd))
          child_kernel := hD2kernel
          parent_kernel_ne := hD1kernel
        }, ?_⟩
        exact Or.inr (Or.inr rfl)

/-- In the kernel-opening alternative, every actual rank-two Hessian witness
on the canonical child is already a rank-two minor of the *original*
singular source F.  This does not assert that every opening has such
a witness. -/
theorem canonicalCodimensionTwoKernel_or_sourceRankTwo_of_childRankTwo
    (F : MvPolynomial (Fin 4) K)
    (hF : F ≠ 0)
    (hzero : HC4.Polynomial.hessianDeterminant F = 0)
    (hnonlinear :
      ∀ d ∈ F.support, 3 ≤ HC4.Polynomial.ordinaryDegree4 d)
    (hcodim :
      MvExponentOnCodimensionTwoBoundary
        (exposedSingularNonlinearBoundaryVertex
          F hF hzero hnonlinear).exponent) :
    (∃ k : Fin 4, MvPolynomial.pderiv k F = 0) ∨
      (∃ O : CanonicalCoordinateMaxKernelOpeningData F,
        O.ChildHessianRankTwoWitness →
          ∃ i j k l : Fin 4,
            hessianTwoByTwoMinor F i j k l ≠ 0) := by
  rcases canonicalCodimensionTwoKernel_or_firstOpening_withProvenance
      F hF hzero hnonlinear hcodim with hkernel | hopen
  · exact Or.inl hkernel
  · rcases hopen with ⟨O, hprov⟩
    right
    refine ⟨O, ?_⟩
    intro htwo
    exact canonicalOpeningRankTwo_source_of_threeFaceProvenance
      F hF O hprov htwo

end
end HC4.Valuation
