import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrLockedSourceCoefficients
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrNormalizedCarrier
import Mathlib.Tactic

/-!
# A19 non-unit quotient orientation fixes the locked source normal form

For `V > 1` there is no remaining transverse-orientation ambiguity.

A normalized quotient carrier of type `(1,V)` has locked direction
`(1,-1,-1,-V)`.  The transverse-swapped locked normal form would instead make
the fourth drop equal to one, forcing `V = 1`.  Hence only the left locked
normal form survives.  The same argument with coordinates `2,3` exchanged
handles quotient type `(V,1)`.

This file is pure source bookkeeping.  It introduces no singularity or clock
comparison and merely synchronizes the `V` appearing in the quotient package
with the `V` in the already-proved locked-ray normal form.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- The exact left locked source data with its transverse drop synchronized to
the non-unit quotient parameter. -/
structure QsOtherFacetPrLockedLeftVSourceData
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    (V : ℕ) where
  ell : ℕ
  ell_pos : 0 < ell
  facet_zero : C.ray.facetExponent 0 = 0
  facet_one : C.ray.facetExponent 1 = 1
  facet_two : C.ray.facetExponent 2 = ell + 1
  facet_three : C.ray.facetExponent 3 = (ell + 1) * V
  outside_zero : C.ray.outsideExponent 0 = 1
  outside_one : C.ray.outsideExponent 1 = 0
  outside_two : C.ray.outsideExponent 2 = ell
  outside_three : C.ray.outsideExponent 3 = ell * V
  facet_provenance :
    QsOtherFacetPrCarrierCoefficientProvenance C P R C.ray.facetExponent
  outside_provenance :
    QsOtherFacetPrCarrierCoefficientProvenance C P R C.ray.outsideExponent

/-- Transverse-swapped version of the exact non-unit locked source data. -/
structure QsOtherFacetPrLockedRightVSourceData
    (C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs)
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    (V : ℕ) where
  ell : ℕ
  ell_pos : 0 < ell
  facet_zero : C.ray.facetExponent 0 = 0
  facet_one : C.ray.facetExponent 1 = 1
  facet_two : C.ray.facetExponent 2 = (ell + 1) * V
  facet_three : C.ray.facetExponent 3 = ell + 1
  outside_zero : C.ray.outsideExponent 0 = 1
  outside_one : C.ray.outsideExponent 1 = 0
  outside_two : C.ray.outsideExponent 2 = ell * V
  outside_three : C.ray.outsideExponent 3 = ell
  facet_provenance :
    QsOtherFacetPrCarrierCoefficientProvenance C P R C.ray.facetExponent
  outside_provenance :
    QsOtherFacetPrCarrierCoefficientProvenance C P R C.ray.outsideExponent

/-- In quotient orientation `(1,V)` with `V>1`, the locked ray is necessarily
the left source normal form with exactly that same `V`. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_locked_leftV_source_data
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    {V : ℕ}
    (hV : 1 < V)
    (Q : QsOtherFacetPrQuotientCarrierData C P 1 V)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    Nonempty (QsOtherFacetPrLockedLeftVSourceData C P R V) := by
  rcases S.pr_locked_source_data_of_nontrivial
      R hthree houtThree hnontrivial with hleft | hright
  · rcases hleft with ⟨D⟩
    have hdir := Q.direction_three
    rw [D.outside_three, D.facet_three] at hdir
    push_cast at hdir
    have hDV : D.V = V := by
      have hz : (D.V : ℤ) = (V : ℤ) := by nlinarith
      exact_mod_cast hz
    subst D.V
    exact ⟨{
      ell := D.ell
      ell_pos := D.ell_pos
      facet_zero := D.facet_zero
      facet_one := D.facet_one
      facet_two := D.facet_two
      facet_three := D.facet_three
      outside_zero := D.outside_zero
      outside_one := D.outside_one
      outside_two := D.outside_two
      outside_three := D.outside_three
      facet_provenance := D.facet_provenance
      outside_provenance := D.outside_provenance
    }⟩
  · rcases hright with ⟨D⟩
    have hdir := Q.direction_three
    rw [D.outside_three, D.facet_three] at hdir
    push_cast at hdir
    have hVone : V = 1 := by
      have hz : (V : ℤ) = 1 := by nlinarith
      exact_mod_cast hz
    omega

/-- In quotient orientation `(V,1)` with `V>1`, only the transverse-swapped
locked source normal form survives, again with the same `V`. -/
theorem QsOtherFacetPlanarHighestPairSlicePackage.pr_locked_rightV_source_data
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    (S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P)
    (R : QsOtherFacetContactQuadraticReesPackage C)
    {V : ℕ}
    (hV : 1 < V)
    (Q : QsOtherFacetPrQuotientCarrierData C P V 1)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hnontrivial :
      ∃ a ∈ S.slice.support, ∃ b ∈ S.slice.support, a ≠ b) :
    Nonempty (QsOtherFacetPrLockedRightVSourceData C P R V) := by
  rcases S.pr_locked_source_data_of_nontrivial
      R hthree houtThree hnontrivial with hleft | hright
  · rcases hleft with ⟨D⟩
    have hdir := Q.direction_two
    rw [D.outside_two, D.facet_two] at hdir
    push_cast at hdir
    have hVone : V = 1 := by
      have hz : (V : ℤ) = 1 := by nlinarith
      exact_mod_cast hz
    omega
  · rcases hright with ⟨D⟩
    have hdir := Q.direction_two
    rw [D.outside_two, D.facet_two] at hdir
    push_cast at hdir
    have hDV : D.V = V := by
      have hz : (D.V : ℤ) = (V : ℤ) := by nlinarith
      exact_mod_cast hz
    subst D.V
    exact ⟨{
      ell := D.ell
      ell_pos := D.ell_pos
      facet_zero := D.facet_zero
      facet_one := D.facet_one
      facet_two := D.facet_two
      facet_three := D.facet_three
      outside_zero := D.outside_zero
      outside_one := D.outside_one
      outside_two := D.outside_two
      outside_three := D.outside_three
      facet_provenance := D.facet_provenance
      outside_provenance := D.outside_provenance
    }⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
