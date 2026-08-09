import HC4.ClassifiedFamilies.BranchConjugacy

/-!
# Unified equivalence for the classified families

The final support classification has two outcomes.  This module packages them
in one datatype and supplies the corresponding gradient map, explicit inverse,
and affine-space equivalence.  A later theorem only needs to produce a branch
witness in order to obtain bijectivity immediately.
-/

namespace HC4.ClassifiedFamilies

/-- Choice of one of the two classified triangular branches. -/
inductive ClassifiedBranch (K : Type*) where
  | r (dP : K → K)
  | s (dP : K → K)

section CommRing

variable {K : Type*} [CommRing K]

/-- Gradient map attached to a classified branch. -/
def classifiedGradient (a b : ℕ) :
    ClassifiedBranch K → Point4 K → Point4 K
  | .r dP => rGradientMap a b dP
  | .s dP => sGradientMap a b dP

/-- Explicit inverse attached to a classified branch. -/
def classifiedInverse (a b : ℕ) :
    ClassifiedBranch K → Point4 K → Point4 K
  | .r dP => rGradientInverse a b dP
  | .s dP => sGradientInverse a b dP

/-- The branch inverse is a left inverse. -/
theorem classifiedInverse_comp_gradient
    (a b : ℕ) (B : ClassifiedBranch K) :
    Function.LeftInverse (classifiedInverse a b B) (classifiedGradient a b B) := by
  cases B with
  | r dP => exact rGradientInverse_comp_map a b dP
  | s dP => exact sGradientInverse_comp_map a b dP

/-- The branch inverse is a right inverse. -/
theorem classifiedGradient_comp_inverse
    (a b : ℕ) (B : ClassifiedBranch K) :
    Function.RightInverse (classifiedInverse a b B) (classifiedGradient a b B) := by
  cases B with
  | r dP => exact rGradientMap_comp_inverse a b dP
  | s dP => exact sGradientMap_comp_inverse a b dP

/-- Every classified gradient map is bijective. -/
theorem classifiedGradient_bijective
    (a b : ℕ) (B : ClassifiedBranch K) :
    Function.Bijective (classifiedGradient a b B) := by
  refine ⟨(classifiedInverse_comp_gradient a b B).injective, ?_⟩
  exact (classifiedGradient_comp_inverse a b B).surjective

/-- Every classified gradient map as an explicit equivalence. -/
def classifiedGradientEquiv
    (a b : ℕ) (B : ClassifiedBranch K) : Point4 K ≃ Point4 K where
  toFun := classifiedGradient a b B
  invFun := classifiedInverse a b B
  left_inv := classifiedInverse_comp_gradient a b B
  right_inv := classifiedGradient_comp_inverse a b B

end CommRing

end HC4.ClassifiedFamilies
