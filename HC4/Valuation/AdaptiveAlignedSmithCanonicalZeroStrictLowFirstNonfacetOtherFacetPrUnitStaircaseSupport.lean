import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitQuotientInterpolation
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneStaircaseSupport
import Mathlib.Tactic

/-!
# A19 unit PR whole-carrier staircase equations

The affine quotient-line argument is independent of the strict non-unit
inequality.  At `V=1` the two generic staircase equations become the symmetric
unit relations.  These statements retain the actual source support and are
used only as input to the already-formalised fibre/first-variation machinery.
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

/-- Exact unit staircase equations in the left highest-slice orientation. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.support_staircase_equations
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    let q := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e
    ((F.highest.n : ℤ) - 1) *
          ((q.firstTransverse : ℤ) - 1) =
        (F.locked.ell : ℤ) *
          ((F.highest.n : ℤ) - (q.pair : ℤ)) ∧
      (q.secondTransverse : ℤ) =
        (q.pair : ℤ) + (q.firstTransverse : ℤ) - 1 := by
  let q := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e
  have hi := F.quotient_affine_interpolation hthree houtThree he
  dsimp only at hi
  have hfirst :
      ((F.highest.n : ℤ) - 1) *
          ((q.firstTransverse : ℤ) - ((F.locked.ell : ℤ) + 1)) =
        ((q.pair : ℤ) - 1) * (1 - ((F.locked.ell : ℤ) + 1)) := by
    simpa [q, HC4.Polynomial.rankThreeQuotientCoordinate,
      F.locked.facet_zero, F.locked.facet_one,
      F.locked.facet_two, F.locked.facet_three,
      F.highest.e0_zero, F.highest.e0_one,
      F.highest.e0_two, F.highest.e0_three,
      F.highest_V_eq_one] using hi.1
  have hsecond :
      ((F.highest.n : ℤ) - 1) *
          ((q.secondTransverse : ℤ) - ((F.locked.ell : ℤ) + 1)) =
        ((q.pair : ℤ) - 1) *
          ((F.highest.n : ℤ) - ((F.locked.ell : ℤ) + 1)) := by
    simpa [q, HC4.Polynomial.rankThreeQuotientCoordinate,
      F.locked.facet_zero, F.locked.facet_one,
      F.locked.facet_two, F.locked.facet_three,
      F.highest.e0_zero, F.highest.e0_one,
      F.highest.e0_two, F.highest.e0_three,
      F.highest_V_eq_one, mul_comm] using hi.2
  have h := left_staircase_equations_of_affine_interpolation
    1 F.locked.ell F.highest.n q F.highest.n_two_le hfirst hsecond
  simpa using h

/-- Exact unit staircase equations in the transverse-swapped orientation. -/
theorem QsOtherFacetPrUnitRightContactFrontierData.support_staircase_equations
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitRightContactFrontierData C P S R)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    {e : Fin 4 →₀ ℕ} (he : e ∈ P.carrier.support) :
    let q := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e
    ((F.highest.n : ℤ) - 1) *
          ((q.secondTransverse : ℤ) - 1) =
        (F.locked.ell : ℤ) *
          ((F.highest.n : ℤ) - (q.pair : ℤ)) ∧
      (q.firstTransverse : ℤ) =
        (q.pair : ℤ) + (q.secondTransverse : ℤ) - 1 := by
  let q := HC4.Polynomial.rankThreeQuotientCoordinate 1 1 e
  have hi := F.quotient_affine_interpolation hthree houtThree he
  dsimp only at hi
  have hfirst :
      ((F.highest.n : ℤ) - 1) *
          ((q.firstTransverse : ℤ) - ((F.locked.ell : ℤ) + 1)) =
        ((q.pair : ℤ) - 1) *
          ((F.highest.n : ℤ) - ((F.locked.ell : ℤ) + 1)) := by
    simpa [q, HC4.Polynomial.rankThreeQuotientCoordinate,
      F.locked.facet_zero, F.locked.facet_one,
      F.locked.facet_two, F.locked.facet_three,
      F.highest.e0_zero, F.highest.e0_one,
      F.highest.e0_two, F.highest.e0_three,
      F.highest_V_eq_one, mul_comm] using hi.1
  have hsecond :
      ((F.highest.n : ℤ) - 1) *
          ((q.secondTransverse : ℤ) - ((F.locked.ell : ℤ) + 1)) =
        ((q.pair : ℤ) - 1) * (1 - ((F.locked.ell : ℤ) + 1)) := by
    simpa [q, HC4.Polynomial.rankThreeQuotientCoordinate,
      F.locked.facet_zero, F.locked.facet_one,
      F.locked.facet_two, F.locked.facet_three,
      F.highest.e0_zero, F.highest.e0_one,
      F.highest.e0_two, F.highest.e0_three,
      F.highest_V_eq_one] using hi.2
  have h := right_staircase_equations_of_affine_interpolation
    1 F.locked.ell F.highest.n q F.highest.n_two_le hfirst hsecond
  simpa using h

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
