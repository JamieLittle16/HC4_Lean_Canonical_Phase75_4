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


/-- Hessian principal minors commute with a coordinate permutation. -/
theorem hessianPrincipalMinor_rename_perm
    (rho : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K)
    (i k : Fin 4) :
    hessianPrincipalMinor (MvPolynomial.rename rho F) i k =
      MvPolynomial.rename rho
        (hessianPrincipalMinor F (rho.symm i) (rho.symm k)) := by
  unfold hessianPrincipalMinor
  have hH := HC4.Newton.hessian_rename_perm (K := K) rho F
  have hii := congrFun (congrFun hH i) i
  have hkk := congrFun (congrFun hH k) k
  have hik := congrFun (congrFun hH i) k
  have hki := congrFun (congrFun hH k) i
  simp only [Matrix.submatrix_apply, RingHom.mapMatrix_apply] at hii hkk hik hki
  rw [hii, hkk, hik, hki]
  simp

/-- Nonvanishing of a renamed principal minor gives nonvanishing of the
corresponding source principal minor. -/
theorem hessianPrincipalMinor_source_ne_zero_of_rename_perm
    (rho : Equiv.Perm (Fin 4))
    (F : MvPolynomial (Fin 4) K)
    (i k : Fin 4)
    (hminor :
      hessianPrincipalMinor (MvPolynomial.rename rho F) i k ≠ 0) :
    hessianPrincipalMinor F (rho.symm i) (rho.symm k) ≠ 0 := by
  intro hzero
  apply hminor
  rw [hessianPrincipalMinor_rename_perm]
  simp [hzero]

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
  have hminor1 : hessianPrincipalMinor D1.face i k ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      D2.weight_bound i k
    simpa [D2.face_eq] using hminor2
  have hminor0 : hessianPrincipalMinor D0.face i k ≠ 0 := by
    apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
      D1.weight_bound i k
    simpa [D1.face_eq] using hminor1
  apply hessianPrincipalMinor_ne_zero_of_initialForm_ne_zero
    D0.weight_bound i k
  simpa [D0.face_eq] using hminor0


/-- A nonzero principal minor on the canonically re-extracted contact-zero ray
lifts to the renamed source polynomial. -/
theorem CrossFacetRayData.renameContactToZero_source_hessianPrincipalMinor_ne_zero
    {F : MvPolynomial (Fin 4) K}
    {j i k : Fin 4}
    (R : CrossFacetRayData F j)
    (hminor :
      hessianPrincipalMinor R.renameContactToZero.face i k ≠ 0) :
    hessianPrincipalMinor
        (MvPolynomial.rename (Equiv.swap j (0 : Fin 4)) F) i k ≠ 0 := by
  let rho : Equiv.Perm (Fin 4) := Equiv.swap j (0 : Fin 4)
  let v : Fin 4 →₀ ℕ := Finsupp.mapDomain rho R.facetExponent
  let o : Fin 4 →₀ ℕ := Finsupp.mapDomain rho R.outsideExponent

  have hvCoeff :
      MvPolynomial.coeff v (MvPolynomial.rename rho F) ≠ 0 := by
    dsimp [v]
    rw [MvPolynomial.coeff_rename_mapDomain
      (rho : Fin 4 → Fin 4) rho.injective]
    exact MvPolynomial.mem_support_iff.mp R.facet_mem_source
  have hoCoeff :
      MvPolynomial.coeff o (MvPolynomial.rename rho F) ≠ 0 := by
    dsimp [o]
    rw [MvPolynomial.coeff_rename_mapDomain
      (rho : Fin 4 → Fin 4) rho.injective]
    exact MvPolynomial.mem_support_iff.mp R.outside_mem_source

  have hvMem :
      v ∈ (MvPolynomial.rename rho F).support :=
    MvPolynomial.mem_support_iff.mpr hvCoeff
  have hoMem :
      o ∈ (MvPolynomial.rename rho F).support :=
    MvPolynomial.mem_support_iff.mpr hoCoeff

  have hv0 : v (0 : Fin 4) = 0 := by
    dsimp [v]
    rw [Finsupp.mapDomain_equiv_apply]
    simpa [rho] using R.facet_coordinate_zero
  have ho0 : 0 < o (0 : Fin 4) := by
    dsimp [o]
    rw [Finsupp.mapDomain_equiv_apply]
    simpa [rho] using R.outside_coordinate_pos

  have hfacet :
      (zeroCoordinateSupport (0 : Fin 4)
        (MvPolynomial.rename rho F)).Nonempty :=
    ⟨v, mem_zeroCoordinateSupport.mpr ⟨hvMem, hv0⟩⟩
  have hout :
      (positiveCoordinateSupport (0 : Fin 4)
        (MvPolynomial.rename rho F)).Nonempty :=
    ⟨o, mem_positiveCoordinateSupport.mpr ⟨hoMem, ho0⟩⟩

  have hminor' :
      hessianPrincipalMinor (crossFacetRayData hfacet hout).face i k ≠ 0 := by
    simpa [CrossFacetRayData.renameContactToZero, rho, v, o] using hminor
  exact crossFacetRayData_source_hessianPrincipalMinor_ne_zero
    hfacet hout hminor'

/-- A minor on the normalized ray therefore lifts all the way back to the
original, unrenamed source in the correspondingly permuted coordinate pair. -/
theorem CrossFacetRayData.source_hessianPrincipalMinor_ne_zero_of_renamedZero
    {F : MvPolynomial (Fin 4) K}
    {j i k : Fin 4}
    (R : CrossFacetRayData F j)
    (hminor :
      hessianPrincipalMinor R.renameContactToZero.face i k ≠ 0) :
    hessianPrincipalMinor F
        ((Equiv.swap j (0 : Fin 4)).symm i)
        ((Equiv.swap j (0 : Fin 4)).symm k) ≠ 0 := by
  exact hessianPrincipalMinor_source_ne_zero_of_rename_perm
    (Equiv.swap j (0 : Fin 4)) F i k
    (R.renameContactToZero_source_hessianPrincipalMinor_ne_zero hminor)

end

end HC4.Valuation
