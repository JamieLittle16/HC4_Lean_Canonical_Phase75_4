import HC4.Newton.FiniteSupportCrossFacetRay
import HC4.Valuation.WeightedHessianPrincipalMinorInitial
import Mathlib.Tactic

/-!
# Lift a canonical cross-facet ray Hessian minor back to its source

`crossFacetRayData` is obtained by three successive exact maximal initial
forms. Nonvanishing of a Hessian principal minor therefore lifts through the
three stages by the generic weighted-initial-form covariance theorem.

This file deliberately treats only the canonical extractor. An arbitrary
manually-constructed `CrossFacetRayData` does not store enough exposure data
to justify the converse lift.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton
open HC4.Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- One exact cross-facet exposure lifts a nonzero principal Hessian minor
from its exposed face to the carrier. -/
theorem CrossFacetInitialData.source_hessianPrincipalMinor_ne_zero
    {F : MvPolynomial (Fin 4) K}
    {a j i k : Fin 4}
    (D : CrossFacetInitialData F a j)
    (hminor : hessianPrincipalMinor D.face i k ≠ 0) :
    hessianPrincipalMinor F i k ≠ 0 := by
  apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    D.weight_bound i k
  simpa [D.face_eq] using hminor

/-- **Canonical three-exposure ray minor lift.**

Any nonzero principal Hessian minor on the exact face returned by
`crossFacetRayData` is already nonzero on the original source polynomial. -/
theorem crossFacetRayData_source_hessianPrincipalMinor_ne_zero
    {F : MvPolynomial (Fin 4) K}
    {j i k : Fin 4}
    (hfacet : (zeroCoordinateSupport j F).Nonempty)
    (hout : (positiveCoordinateSupport j F).Nonempty)
    (hminor :
      hessianPrincipalMinor (crossFacetRayData hfacet hout).face i k ≠ 0) :
    hessianPrincipalMinor F i k ≠ 0 := by
  let D0 := crossFacetInitialData
    (i := crossFacetRayAux0 j) (j := j) hfacet hout
  have hfacet1 : (zeroCoordinateSupport j D0.face).Nonempty := by
    exact ⟨D0.facetExponent,
      mem_zeroCoordinateSupport.mpr
        ⟨D0.facet_mem_face, D0.facet_coordinate_zero⟩⟩
  have hout1 : (positiveCoordinateSupport j D0.face).Nonempty := by
    exact ⟨D0.outsideExponent,
      mem_positiveCoordinateSupport.mpr
        ⟨D0.outside_mem_face, D0.outside_coordinate_pos⟩⟩
  let D1 := crossFacetInitialData
    (i := crossFacetRayAux1 j) (j := j) hfacet1 hout1
  have hfacet2 : (zeroCoordinateSupport j D1.face).Nonempty := by
    exact ⟨D1.facetExponent,
      mem_zeroCoordinateSupport.mpr
        ⟨D1.facet_mem_face, D1.facet_coordinate_zero⟩⟩
  have hout2 : (positiveCoordinateSupport j D1.face).Nonempty := by
    exact ⟨D1.outsideExponent,
      mem_positiveCoordinateSupport.mpr
        ⟨D1.outside_mem_face, D1.outside_coordinate_pos⟩⟩
  let D2 := crossFacetInitialData
    (i := crossFacetRayAux2 j) (j := j) hfacet2 hout2

  have hminor2 : hessianPrincipalMinor D2.face i k ≠ 0 := by
    change hessianPrincipalMinor D2.face i k ≠ 0 at hminor
    exact hminor
  have hminor1 : hessianPrincipalMinor D1.face i k ≠ 0 :=
    D2.source_hessianPrincipalMinor_ne_zero hminor2
  have hminor0 : hessianPrincipalMinor D0.face i k ≠ 0 :=
    D1.source_hessianPrincipalMinor_ne_zero hminor1
  exact D0.source_hessianPrincipalMinor_ne_zero hminor0

end

end HC4.Valuation
