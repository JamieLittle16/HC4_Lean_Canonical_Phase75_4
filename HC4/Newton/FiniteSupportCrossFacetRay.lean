import HC4.Newton.FiniteSupportCrossFacetExposure
import HC4.Newton.SingularBoundaryRankSplit
import Mathlib.Tactic

/-!
# A19.67: balance-free finite-support cross-facet ray exposure

The older cross-facet affine-line adapter used a torus-balance equation as one
of three independent affine equations.  That hypothesis is not available in
the unrestricted zero-clock branch.

Finite support supplies a grading-free replacement.  Starting from any carrier
with support on both sides of the coordinate facet `d j = 0`, apply the honest
cross-facet exposure successively in the three coordinates different from
`j`.  Each stage retains a facet point and an outside point and passes Hessian
singularity to an exact initial form.  On the final face the three exact
secondary-weight equations force every supported exponent to be proportional
to the certified facet-to-outside direction.

Thus the final carrier is an honest affine support ray without any torus
balance, cocharacter, or homogeneity assumption.  Its facet endpoint remains
an actual coordinate-boundary exponent and hence is either rank three or
codimension two.
-/

namespace HC4.Newton

open HC4.Polynomial
open MvPolynomial

noncomputable section

universe u
variable {K : Type u} [Field K] [CharZero K]

/-- First auxiliary coordinate in the canonical enumeration of the three
coordinates different from `j`. -/
def crossFacetRayAux0 (j : Fin 4) : Fin 4 :=
  ![(1 : Fin 4), 0, 0, 0] j

/-- Second auxiliary coordinate different from `j`. -/
def crossFacetRayAux1 (j : Fin 4) : Fin 4 :=
  ![(2 : Fin 4), 2, 1, 1] j

/-- Third auxiliary coordinate different from `j`. -/
def crossFacetRayAux2 (j : Fin 4) : Fin 4 :=
  ![(3 : Fin 4), 3, 3, 2] j

/-- Every supported exponent of the exact finite cross-facet face lies on the
stored secondary exposing level.  This is immediate from `face_eq` and the
coefficient formula for `initialForm`; it is kept here because A18.5.65c did
not need to expose it as a structure field. -/
theorem CrossFacetInitialData.face_weight_eq
    {F : MvPolynomial (Fin 4) K} {i j : Fin 4}
    (D : CrossFacetInitialData F i j)
    {d : Fin 4 →₀ ℕ}
    (hd : d ∈ D.face.support) :
    Finsupp.weight (crossFacetWeight i j D.scale D.bump) d = D.level := by
  rw [D.face_eq] at hd
  have hne := MvPolynomial.mem_support_iff.mp hd
  rw [coeff_initialForm] at hne
  by_cases hw :
      Finsupp.weight (crossFacetWeight i j D.scale D.bump) d = D.level
  · exact hw
  · simp [hw] at hne

/-- One secondary cross-facet face gives an exact proportionality equation in
its auxiliary coordinate for any three supported points, provided the chosen
base point is on the contact facet. -/
theorem CrossFacetInitialData.auxiliary_cross_proportional
    {F : MvPolynomial (Fin 4) K} {i j : Fin 4}
    (D : CrossFacetInitialData F i j)
    {v o d : Fin 4 →₀ ℕ}
    (hv : v ∈ D.face.support)
    (ho : o ∈ D.face.support)
    (hd : d ∈ D.face.support)
    (hvj : v j = 0) :
    (o j : ℤ) * ((d i : ℤ) - (v i : ℤ)) =
      (d j : ℤ) * ((o i : ℤ) - (v i : ℤ)) := by
  have hvw := D.face_weight_eq hv
  have how := D.face_weight_eq ho
  have hdw := D.face_weight_eq hd
  rw [weight_crossFacetWeight] at hvw how hdw
  rw [hvj] at hvw
  simp only [Nat.cast_zero, mul_zero, add_zero] at hvw
  have hdifference :
      (D.scale : ℤ) * ((d i : ℤ) - (v i : ℤ)) +
        (D.bump : ℤ) * (d j : ℤ) = 0 := by
    linear_combination hdw - hvw
  have hodifference :
      (D.scale : ℤ) * ((o i : ℤ) - (v i : ℤ)) +
        (D.bump : ℤ) * (o j : ℤ) = 0 := by
    linear_combination how - hvw
  have hscaled :
      (D.scale : ℤ) *
          ((o j : ℤ) * ((d i : ℤ) - (v i : ℤ)) -
            (d j : ℤ) * ((o i : ℤ) - (v i : ℤ))) = 0 := by
    linear_combination (o j : ℤ) * hdifference - (d j : ℤ) * hodifference
  have hscale : (D.scale : ℤ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt D.scale_pos)
  have hcross :
      (o j : ℤ) * ((d i : ℤ) - (v i : ℤ)) -
          (d j : ℤ) * ((o i : ℤ) - (v i : ℤ)) = 0 :=
    (mul_eq_zero.mp hscaled).resolve_left hscale
  exact sub_eq_zero.mp hcross

/-- Complete balance-free affine-ray carrier obtained by three successive
finite cross-facet exposures. -/
structure CrossFacetRayData
    (F : MvPolynomial (Fin 4) K) (j : Fin 4) : Type (u + 1) where
  face : MvPolynomial (Fin 4) K
  facetExponent : Fin 4 →₀ ℕ
  outsideExponent : Fin 4 →₀ ℕ
  facet_mem_source : facetExponent ∈ F.support
  outside_mem_source : outsideExponent ∈ F.support
  facet_mem_face : facetExponent ∈ face.support
  outside_mem_face : outsideExponent ∈ face.support
  facet_coordinate_zero : facetExponent j = 0
  outside_coordinate_pos : 0 < outsideExponent j
  support_subset : face.support ⊆ F.support
  hessian_zero_of_source :
    hessianDeterminant F = 0 → hessianDeterminant face = 0
  affine_proportional :
    ∀ d ∈ face.support, ∀ k : Fin 4,
      (outsideExponent j : ℤ) *
          ((d k : ℤ) - (facetExponent k : ℤ)) =
        (d j : ℤ) *
          ((outsideExponent k : ℤ) - (facetExponent k : ℤ))

/-- **Balance-free cross-facet ray extraction.**

Three successive exact finite-support exposures, one in each non-contact
coordinate, force the surviving support onto a single affine ray through an
actual facet exponent and an actual outside exponent. -/
noncomputable def crossFacetRayData
    {F : MvPolynomial (Fin 4) K} {j : Fin 4}
    (hfacet : (zeroCoordinateSupport j F).Nonempty)
    (hout : (positiveCoordinateSupport j F).Nonempty) :
    CrossFacetRayData F j := by
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

  have hD2D1 : D2.face.support ⊆ D1.face.support := D2.support_subset
  have hD1D0 : D1.face.support ⊆ D0.face.support := D1.support_subset
  have hD0F : D0.face.support ⊆ F.support := D0.support_subset

  refine {
    face := D2.face
    facetExponent := D2.facetExponent
    outsideExponent := D2.outsideExponent
    facet_mem_source := hD0F (hD1D0 (hD2D1 D2.facet_mem_face))
    outside_mem_source := hD0F (hD1D0 (hD2D1 D2.outside_mem_face))
    facet_mem_face := D2.facet_mem_face
    outside_mem_face := D2.outside_mem_face
    facet_coordinate_zero := D2.facet_coordinate_zero
    outside_coordinate_pos := D2.outside_coordinate_pos
    support_subset := fun d hd => hD0F (hD1D0 (hD2D1 hd))
    hessian_zero_of_source := by
      intro hzero
      exact D2.hessian_zero (D1.hessian_zero (D0.hessian_zero hzero))
    affine_proportional := ?_
  }

  intro d hd k
  have hv2 : D2.facetExponent ∈ D2.face.support := D2.facet_mem_face
  have ho2 : D2.outsideExponent ∈ D2.face.support := D2.outside_mem_face
  have hv1 : D2.facetExponent ∈ D1.face.support := hD2D1 hv2
  have ho1 : D2.outsideExponent ∈ D1.face.support := hD2D1 ho2
  have hd1 : d ∈ D1.face.support := hD2D1 hd
  have hv0 : D2.facetExponent ∈ D0.face.support := hD1D0 hv1
  have ho0 : D2.outsideExponent ∈ D0.face.support := hD1D0 ho1
  have hd0 : d ∈ D0.face.support := hD1D0 hd1
  have hvj : D2.facetExponent j = 0 := D2.facet_coordinate_zero

  have haux0 := D0.auxiliary_cross_proportional hv0 ho0 hd0 hvj
  have haux1 := D1.auxiliary_cross_proportional hv1 ho1 hd1 hvj
  have haux2 := D2.auxiliary_cross_proportional hv2 ho2 hd hvj

  have hk :
      k = j ∨ k = crossFacetRayAux0 j ∨
        k = crossFacetRayAux1 j ∨ k = crossFacetRayAux2 j := by
    fin_cases j <;> fin_cases k <;>
      simp [crossFacetRayAux0, crossFacetRayAux1, crossFacetRayAux2]
  rcases hk with rfl | hk0 | hk1 | hk2
  · rw [hvj]
    ring
  · simpa [hk0] using haux0
  · simpa [hk1] using haux1
  · simpa [hk2] using haux2

/-- The ray facet endpoint is an actual coordinate-boundary exponent, hence it
has the same balance-free rank-three/codimension-two split as A18.5.93. -/
theorem CrossFacetRayData.rankThreeFacet_or_codimensionTwo
    {F : MvPolynomial (Fin 4) K} {j : Fin 4}
    (R : CrossFacetRayData F j) :
    (∃ facet : HC4.Toric.ToricFacet,
        MvRankThreeOnFacet facet R.facetExponent) ∨
      MvExponentOnCodimensionTwoBoundary R.facetExponent := by
  apply mvBoundary_rankThreeFacet_or_codimensionTwo
  rw [mvExponentOnBoundary_iff_coordinate_zero]
  fin_cases j
  · exact Or.inl R.facet_coordinate_zero
  · exact Or.inr (Or.inl R.facet_coordinate_zero)
  · exact Or.inr (Or.inr (Or.inl R.facet_coordinate_zero))
  · exact Or.inr (Or.inr (Or.inr R.facet_coordinate_zero))

end

end HC4.Newton
