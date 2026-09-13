import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrQuotientFiber
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPlanarLineSupport
import Mathlib.Tactic

/-!
# A19 PR planar carrier quotient fibers

The highest-slice adapter already identifies the primitive top slice with one
rank-three quotient fiber.  The same quotient statement is true for every
fixed pair-degree slice of the source-honest planar carrier: the general
line-support theorem says that two support exponents of equal pair degree
differ by an integer multiple of the locked source direction
`(1,-1,-alpha,-beta)`, and the quotient coordinates are precisely the three
invariants of that direction.

This file records that global carrier fact without asserting that every fiber
is non-singleton or singular.  Those are separate geometric issues in the
singleton/no-singleton split.
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

/-- Any two monomials of the actual `.pr` planar carrier with the same pair
degree lie in the same quotient fiber of the locked rank-three direction. -/
theorem QsOtherFacetPlanarCarrierPackage.pr_quotient_eq_of_pairDegree_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (D : QsPrLockedQuotientData C)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) (hf : f ∈ P.carrier.support)
    (hpair : qsOtherFacetPairDegree .pr e =
      qsOtherFacetPairDegree .pr f) :
    rankThreeQuotientCoordinate D.alpha D.beta e =
      rankThreeQuotientCoordinate D.alpha D.beta f := by
  have hpar := P.support_difference_parallel_ray
    hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree he hf hpair
  have hdir := D.direction_eq hthree houtThree
  rcases hdir with ⟨_hd0, hd1, hd2, hd3⟩
  have h1 := hpar (1 : Fin 4)
  have h2 := hpar (2 : Fin 4)
  have h3 := hpar (3 : Fin 4)
  rw [hd1] at h1
  rw [hd2] at h2
  rw [hd3] at h3
  rw [rankThreeQuotientCoordinate_eq_iff]
  constructor
  · exact_mod_cast (show
      (e 0 : ℤ) + (e 1 : ℤ) = (f 0 : ℤ) + (f 1 : ℤ) by
        nlinarith [h1])
  constructor
  · exact_mod_cast (show
      (D.alpha : ℤ) * (e 0 : ℤ) + (e 2 : ℤ) =
        (D.alpha : ℤ) * (f 0 : ℤ) + (f 2 : ℤ) by
        nlinarith [h2])
  · exact_mod_cast (show
      (D.beta : ℤ) * (e 0 : ℤ) + (e 3 : ℤ) =
        (D.beta : ℤ) * (f 0 : ℤ) + (f 3 : ℤ) by
        nlinarith [h3])

/-- The quotient drop data can be chosen canonically, so callers do not need
to thread it merely to use the fixed-pair fiber property. -/
theorem QsOtherFacetPlanarCarrierPackage.exists_pr_quotient_data_and_fiber_rule
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    ∃ D : QsPrLockedQuotientData C,
      ∀ {e f : Fin 4 →₀ ℕ},
        e ∈ P.carrier.support → f ∈ P.carrier.support →
        qsOtherFacetPairDegree .pr e = qsOtherFacetPairDegree .pr f →
        rankThreeQuotientCoordinate D.alpha D.beta e =
          rankThreeQuotientCoordinate D.alpha D.beta f := by
  let D := C.qsPrLockedQuotientData hthree houtThree
  exact ⟨D, fun he hf hpair =>
    P.pr_quotient_eq_of_pairDegree_eq hthree houtThree D he hf hpair⟩

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
