import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrPrimitiveDirection
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrPlanarQuotientFibers
import Mathlib.Tactic

/-!
# A19 normalized PR quotient fibers

After the primitive highest slice has normalized the common locked direction,
the quotient coordinates can be written directly with the paper parameter `V`.
For direction `(1,-1,-1,-V)` the invariants on every fixed pair-degree slice
are

    e0 + e1,  e0 + e2,  V*e0 + e3.

For the transverse swap `(1,-1,-V,-1)`, they are

    e0 + e1,  V*e0 + e2,  e0 + e3.

These are source-facing statements about the whole planar carrier, not just the
highest slice.
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

/-- Fixed pair-degree slices are `(1,V)` quotient fibers in the first primitive
orientation. -/
theorem QsOtherFacetPlanarCarrierPackage.pr_quotient_eq_of_normalized_left
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {V : ℕ}
    (hdir2 :
      (C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) = -1)
    (hdir3 :
      (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) =
        -(V : ℤ))
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) (hf : f ∈ P.carrier.support)
    (hpair : qsOtherFacetPairDegree .pr e =
      qsOtherFacetPairDegree .pr f) :
    rankThreeQuotientCoordinate 1 V e =
      rankThreeQuotientCoordinate 1 V f := by
  have hpar := P.support_difference_parallel_ray
    hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree he hf hpair
  have h2 := hpar (2 : Fin 4)
  have h3 := hpar (3 : Fin 4)
  rw [hdir2] at h2
  rw [hdir3] at h3
  rw [rankThreeQuotientCoordinate_eq_iff]
  constructor
  · simpa [qsOtherFacetPairDegree] using hpair
  constructor
  · exact_mod_cast (show
      (e 0 : ℤ) + (e 2 : ℤ) = (f 0 : ℤ) + (f 2 : ℤ) by
        nlinarith [h2])
  · exact_mod_cast (show
      (V : ℤ) * (e 0 : ℤ) + (e 3 : ℤ) =
        (V : ℤ) * (f 0 : ℤ) + (f 3 : ℤ) by
        nlinarith [h3])

/-- Fixed pair-degree slices are `(V,1)` quotient fibers in the swapped
primitive orientation. -/
theorem QsOtherFacetPlanarCarrierPackage.pr_quotient_eq_of_normalized_right
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    (P : QsOtherFacetPlanarCarrierPackage C .pr)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {V : ℕ}
    (hdir2 :
      (C.ray.outsideExponent 2 : ℤ) - (C.ray.facetExponent 2 : ℤ) =
        -(V : ℤ))
    (hdir3 :
      (C.ray.outsideExponent 3 : ℤ) - (C.ray.facetExponent 3 : ℤ) = -1)
    {e f : Fin 4 →₀ ℕ}
    (he : e ∈ P.carrier.support) (hf : f ∈ P.carrier.support)
    (hpair : qsOtherFacetPairDegree .pr e =
      qsOtherFacetPairDegree .pr f) :
    rankThreeQuotientCoordinate V 1 e =
      rankThreeQuotientCoordinate V 1 f := by
  have hpar := P.support_difference_parallel_ray
    hthree (by decide : (.pr : ToricFacet) ≠ .qs) houtThree he hf hpair
  have h2 := hpar (2 : Fin 4)
  have h3 := hpar (3 : Fin 4)
  rw [hdir2] at h2
  rw [hdir3] at h3
  rw [rankThreeQuotientCoordinate_eq_iff]
  constructor
  · simpa [qsOtherFacetPairDegree] using hpair
  constructor
  · exact_mod_cast (show
      (V : ℤ) * (e 0 : ℤ) + (e 2 : ℤ) =
        (V : ℤ) * (f 0 : ℤ) + (f 2 : ℤ) by
        nlinarith [h2])
  · exact_mod_cast (show
      (e 0 : ℤ) + (e 3 : ℤ) = (f 0 : ℤ) + (f 3 : ℤ) by
        nlinarith [h3])

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
