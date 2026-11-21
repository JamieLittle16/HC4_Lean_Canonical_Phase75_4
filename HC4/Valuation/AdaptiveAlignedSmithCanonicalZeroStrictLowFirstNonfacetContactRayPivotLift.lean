import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetEulerPivot
import HC4.Valuation.WeightedHessianPrincipalMinorInitial
import HC4.Newton.FiniteSupportCrossFacetRay
import Mathlib.Tactic

/-!
# A19.R18: lift the locked-ray pivots back to the contact face

The balance-free ray is produced by three successive exact maximal initial
forms inside the first-contact carrier.  Nonvanishing of a Hessian principal
minor on the final ray therefore propagates backwards through those three
initial forms to the original contact face.

This is the missing direction needed for the binary active valuation.  It uses
only the finite-support construction already stored by `crossFacetRayData` and
the generic Hessian-principal-minor initial-form covariance.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial
open HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

/-- A nonzero principal minor on the canonical three-stage cross-facet ray
forces the same principal minor to be nonzero on its source carrier. -/
theorem hessianPrincipalMinor_ne_zero_of_crossFacetRay
    {F : MvPolynomial (Fin 4) K} {j : Fin 4}
    (hfacet : (HC4.Newton.zeroCoordinateSupport j F).Nonempty)
    (hout : (HC4.Newton.positiveCoordinateSupport j F).Nonempty)
    (i k : Fin 4)
    (hminor :
      HC4.Polynomial.hessianPrincipalMinor
        (HC4.Newton.crossFacetRayData hfacet hout).face i k ≠ 0) :
    HC4.Polynomial.hessianPrincipalMinor F i k ≠ 0 := by
  let D0 := HC4.Newton.crossFacetInitialData
    (i := HC4.Newton.crossFacetRayAux0 j) (j := j) hfacet hout
  have hfacet1 :
      (HC4.Newton.zeroCoordinateSupport j D0.face).Nonempty := by
    exact ⟨D0.facetExponent,
      HC4.Newton.mem_zeroCoordinateSupport.mpr
        ⟨D0.facet_mem_face, D0.facet_coordinate_zero⟩⟩
  have hout1 :
      (HC4.Newton.positiveCoordinateSupport j D0.face).Nonempty := by
    exact ⟨D0.outsideExponent,
      HC4.Newton.mem_positiveCoordinateSupport.mpr
        ⟨D0.outside_mem_face, D0.outside_coordinate_pos⟩⟩
  let D1 := HC4.Newton.crossFacetInitialData
    (i := HC4.Newton.crossFacetRayAux1 j) (j := j) hfacet1 hout1
  have hfacet2 :
      (HC4.Newton.zeroCoordinateSupport j D1.face).Nonempty := by
    exact ⟨D1.facetExponent,
      HC4.Newton.mem_zeroCoordinateSupport.mpr
        ⟨D1.facet_mem_face, D1.facet_coordinate_zero⟩⟩
  have hout2 :
      (HC4.Newton.positiveCoordinateSupport j D1.face).Nonempty := by
    exact ⟨D1.outsideExponent,
      HC4.Newton.mem_positiveCoordinateSupport.mpr
        ⟨D1.outside_mem_face, D1.outside_coordinate_pos⟩⟩
  let D2 := HC4.Newton.crossFacetInitialData
    (i := HC4.Newton.crossFacetRayAux2 j) (j := j) hfacet2 hout2
  have hray :
      (HC4.Newton.crossFacetRayData hfacet hout).face = D2.face := by
    rfl
  have h2 : HC4.Polynomial.hessianPrincipalMinor D2.face i k ≠ 0 := by
    simpa [hray] using hminor
  have h1 : HC4.Polynomial.hessianPrincipalMinor D1.face i k ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      D2.weight_bound i k
    rw [← D2.face_eq]
    exact h2
  have h0 : HC4.Polynomial.hessianPrincipalMinor D0.face i k ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      D1.weight_bound i k
    rw [← D1.face_eq]
    exact h1
  apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    D0.weight_bound i k
  rw [← D0.face_eq]
  exact h0

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- `.pr`: the `(2,3)` pivot already exists on the original first-contact
carrier, before any secondary ray refinement. -/
theorem qs_contactFace_pr_hessianPrincipalMinor_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    HC4.Polynomial.hessianPrincipalMinor C.face (2 : Fin 4) 3 ≠ 0 := by
  apply hessianPrincipalMinor_ne_zero_of_crossFacetRay
    C.zero_and_positive_support_nonempty.1
    C.zero_and_positive_support_nonempty.2
    (2 : Fin 4) 3
  change HC4.Polynomial.hessianPrincipalMinor C.ray.face (2 : Fin 4) 3 ≠ 0
  exact HC4.Polynomial.hessianPrincipalMinor_ne_zero_of_eulerScaled_ne_zero
    C.ray.face (2 : Fin 4) 3
    (C.qs_ray_pr_eulerScaledHessianPrincipalMinor_ne_zero hthree houtThree)

/-- `.sp`: the `(1,3)` pivot lifts from the ray to the contact face. -/
theorem qs_contactFace_sp_hessianPrincipalMinor_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .sp C.ray.outsideExponent) :
    HC4.Polynomial.hessianPrincipalMinor C.face (1 : Fin 4) 3 ≠ 0 := by
  apply hessianPrincipalMinor_ne_zero_of_crossFacetRay
    C.zero_and_positive_support_nonempty.1
    C.zero_and_positive_support_nonempty.2
    (1 : Fin 4) 3
  change HC4.Polynomial.hessianPrincipalMinor C.ray.face (1 : Fin 4) 3 ≠ 0
  exact HC4.Polynomial.hessianPrincipalMinor_ne_zero_of_eulerScaled_ne_zero
    C.ray.face (1 : Fin 4) 3
    (C.qs_ray_sp_eulerScaledHessianPrincipalMinor_ne_zero hthree houtThree)

/-- `.rq`: the `(1,2)` pivot lifts from the ray to the contact face. -/
theorem qs_contactFace_rq_hessianPrincipalMinor_ne_zero
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (hthree : HC4.Newton.MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : HC4.Newton.MvRankThreeOnFacet .rq C.ray.outsideExponent) :
    HC4.Polynomial.hessianPrincipalMinor C.face (1 : Fin 4) 2 ≠ 0 := by
  apply hessianPrincipalMinor_ne_zero_of_crossFacetRay
    C.zero_and_positive_support_nonempty.1
    C.zero_and_positive_support_nonempty.2
    (1 : Fin 4) 2
  change HC4.Polynomial.hessianPrincipalMinor C.ray.face (1 : Fin 4) 2 ≠ 0
  exact HC4.Polynomial.hessianPrincipalMinor_ne_zero_of_eulerScaled_ne_zero
    C.ray.face (1 : Fin 4) 2
    (C.qs_ray_rq_eulerScaledHessianPrincipalMinor_ne_zero hthree houtThree)

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
