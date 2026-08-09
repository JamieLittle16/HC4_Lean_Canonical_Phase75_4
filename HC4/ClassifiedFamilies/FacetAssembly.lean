import HC4.ClassifiedFamilies.ClassifiedEquiv
import HC4.Toric.Facets

/-!
# Assembly of the four facet outcomes

The two `r`-adjacent facets lead to the `r` shear family, while the two
`s`-adjacent facets lead to the `s` family.  This module packages the four
geometric outcomes and immediately supplies the explicit polynomial
automorphism established for the corresponding classified branch.
-/

namespace HC4.ClassifiedFamilies

open HC4.Toric

/-- A classified outcome retaining which toric facet contained the nonlinear support. -/
inductive FacetOutcome (K : Type*) where
  | pr (dP : K → K)
  | rq (dP : K → K)
  | qs (dP : K → K)
  | sp (dP : K → K)

/-- Forget the facet label and retain the corresponding triangular branch. -/
def FacetOutcome.toClassifiedBranch {K : Type*} :
    FacetOutcome K → ClassifiedBranch K
  | .pr dP => .r dP
  | .rq dP => .r dP
  | .qs dP => .s dP
  | .sp dP => .s dP

/-- The toric facet associated with an outcome. -/
def FacetOutcome.facet {K : Type*} : FacetOutcome K → ToricFacet
  | .pr _ => .pr
  | .rq _ => .rq
  | .qs _ => .qs
  | .sp _ => .sp

section CommRing

variable {K : Type*} [CommRing K]

/-- Gradient map attached to a facet-classified outcome. -/
def facetGradient (a b : ℕ) (O : FacetOutcome K) : Point4 K → Point4 K :=
  classifiedGradient a b O.toClassifiedBranch

/-- Explicit inverse attached to a facet-classified outcome. -/
def facetInverse (a b : ℕ) (O : FacetOutcome K) : Point4 K → Point4 K :=
  classifiedInverse a b O.toClassifiedBranch

/-- The explicit facet inverse is a left inverse. -/
theorem facetInverse_comp_gradient
    (a b : ℕ) (O : FacetOutcome K) :
    Function.LeftInverse (facetInverse a b O) (facetGradient a b O) := by
  exact classifiedInverse_comp_gradient a b O.toClassifiedBranch

/-- The explicit facet inverse is a right inverse. -/
theorem facetGradient_comp_inverse
    (a b : ℕ) (O : FacetOutcome K) :
    Function.RightInverse (facetInverse a b O) (facetGradient a b O) := by
  exact classifiedGradient_comp_inverse a b O.toClassifiedBranch

/-- Every one of the four facet outcomes gives a polynomial bijection. -/
theorem facetGradient_bijective
    (a b : ℕ) (O : FacetOutcome K) :
    Function.Bijective (facetGradient a b O) := by
  exact classifiedGradient_bijective a b O.toClassifiedBranch

/-- Every facet outcome as an explicit affine-space equivalence. -/
def facetGradientEquiv
    (a b : ℕ) (O : FacetOutcome K) : Point4 K ≃ Point4 K :=
  classifiedGradientEquiv a b O.toClassifiedBranch

end CommRing

end HC4.ClassifiedFamilies
