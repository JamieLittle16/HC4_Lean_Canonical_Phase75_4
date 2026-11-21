import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOneFiniteStaircaseOneFiberDegree
import HC4.Polynomial.FiniteStaircaseModeLeading
import Mathlib.Tactic

/-!
# A19 honest leading longitudinal modes in the one-fibre branch

On the two extreme diagonals the dual endpoint Euler degree constraints already
force the *ordinary* degree of the honest common source profile:

* `j=k`     gives degree exactly `k`;
* `j+2=k`   gives degree exactly `k-1`.

Hence the corresponding top coefficient is nonzero.  The generic staircase
moment coefficient formulas then identify the top longitudinal matrix of the
honest interior layer with the numerical exponent cores used by the pure-mode
second-variation calculation.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open scoped Matrix

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

/-- Upper extreme `j=k`: the honest common profile has degree exactly `k`. -/
theorem QsOtherFacetPrLeftVContactFrontierData.oneFiber_upper_profile_natDegree_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F Dhi)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hext : Alo.k = Ahi.k)
    (hdiag : Alo.j = Alo.k) :
    Alo.coefficientProfile.natDegree = Alo.k := by
  rcases F.oneFiber_commonProfile_degree_pairs
      Alo Ahi hthree houtThree hext with ⟨hlo, hhi⟩
  rcases hlo with hlo | hlo <;> rcases hhi with hhi | hhi <;> omega

/-- Lower extreme `j+2=k`: the honest common profile has degree exactly
`k-1`. -/
theorem QsOtherFacetPrLeftVContactFrontierData.oneFiber_lower_profile_natDegree_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F Dhi)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hext : Alo.k = Ahi.k)
    (hdiag : Alo.j + 2 = Alo.k) :
    Alo.coefficientProfile.natDegree = Alo.k - 1 := by
  rcases F.oneFiber_commonProfile_degree_pairs
      Alo Ahi hthree houtThree hext with ⟨hlo, hhi⟩
  rcases hlo with hlo | hlo <;> rcases hhi with hhi | hhi <;> omega

/-- The upper top profile coefficient is nonzero. -/
theorem QsOtherFacetPrLeftVContactFrontierData.oneFiber_upper_profile_top_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F Dhi)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hext : Alo.k = Ahi.k)
    (hdiag : Alo.j = Alo.k) :
    Alo.coefficientProfile.coeff Alo.k ≠ 0 := by
  have hdeg := F.oneFiber_upper_profile_natDegree_eq
    Alo Ahi hthree houtThree hext hdiag
  have hlead : Alo.coefficientProfile.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr Alo.coefficientProfile_ne_zero
  simpa [Polynomial.leadingCoeff, hdeg] using hlead

/-- The lower top profile coefficient is nonzero. -/
theorem QsOtherFacetPrLeftVContactFrontierData.oneFiber_lower_profile_top_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrPairFirstInteriorAffineLayerData F Dhi)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hext : Alo.k = Ahi.k)
    (hdiag : Alo.j + 2 = Alo.k) :
    Alo.coefficientProfile.coeff (Alo.k - 1) ≠ 0 := by
  have hdeg := F.oneFiber_lower_profile_natDegree_eq
    Alo Ahi hthree houtThree hext hdiag
  have hlead : Alo.coefficientProfile.leadingCoeff ≠ 0 :=
    Polynomial.leadingCoeff_ne_zero.mpr Alo.coefficientProfile_ne_zero
  simpa [Polynomial.leadingCoeff, hdeg] using hlead

/-- Upper honest interior moment matrix at its top longitudinal degree. -/
theorem QsOtherFacetPrLeftVContactFrontierData.oneFiber_upper_moment_top_coeff
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    (hdiag : Alo.j = Alo.k) :
    (fun r s =>
      (parallelStaircaseMomentHessian F.V Alo.k Alo.j
        Alo.coefficientProfile r s).coeff Alo.k) =
      Alo.coefficientProfile.coeff Alo.k •
        fieldExponentHessianCore
          ![(Alo.k : K), 0, 1, (F.V : K) * (Alo.k : K)] := by
  subst Alo.j
  exact HC4.Polynomial.coeff_upperMode_parallelStaircase
    F.V Alo.k Alo.coefficientProfile

/-- Lower honest interior moment matrix at its top longitudinal degree. -/
theorem QsOtherFacetPrLeftVContactFrontierData.oneFiber_lower_moment_top_coeff
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrLeftVContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrLeftVPlanarContactReesData F}
    (Alo : QsOtherFacetPrLeftVFirstInteriorAffineLayerData Dlo)
    (hdiag : Alo.j + 2 = Alo.k) :
    (fun r s =>
      (parallelStaircaseMomentHessian F.V Alo.k Alo.j
        Alo.coefficientProfile r s).coeff (Alo.k - 1)) =
      Alo.coefficientProfile.coeff (Alo.k - 1) •
        fieldExponentHessianCore
          ![((Alo.k - 1 : ℕ) : K), 1, 0,
            (F.V : K) * ((Alo.k - 1 : ℕ) : K)] := by
  have hk : 2 ≤ Alo.k := by omega
  have hj : Alo.j = Alo.k - 2 := by omega
  rw [hj]
  exact HC4.Polynomial.coeff_lowerMode_parallelStaircase
    F.V Alo.k hk Alo.coefficientProfile

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
