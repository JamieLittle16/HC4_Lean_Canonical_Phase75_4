import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrUnitFiniteStaircaseOneFiberDegree
import HC4.Polynomial.FiniteStaircaseModeLeading
import Mathlib.Tactic

/-!
# A19 unit one-fibre leading longitudinal modes

On the two extreme unit diagonals, the already-verified dual endpoint Euler
degree constraints force the ordinary degree of the common source profile.
The generic staircase moment coefficient identities then give the exact top
longitudinal matrices, specialised at quotient parameter `V = 1`.
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

/-- Upper extreme `j=k`: the honest common unit profile has degree exactly `k`. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.oneFiber_upper_profile_natDegree_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData F Dhi)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hext : Alo.k = Ahi.k)
    (hdiag : Alo.j = Alo.k) :
    Alo.coefficientProfile.natDegree = Alo.k := by
  rcases F.oneFiber_commonProfile_degree_pairs
      Alo Ahi hthree houtThree hext with ⟨hlo, hhi⟩
  rcases hlo with hlo | hlo <;> rcases hhi with hhi | hhi <;> omega

/-- Lower extreme `j+2=k`: the honest common unit profile has degree `k-1`. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.oneFiber_lower_profile_natDegree_eq
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData F Dhi)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (hext : Alo.k = Ahi.k)
    (hdiag : Alo.j + 2 = Alo.k) :
    Alo.coefficientProfile.natDegree = Alo.k - 1 := by
  rcases F.oneFiber_commonProfile_degree_pairs
      Alo Ahi hthree houtThree hext with ⟨hlo, hhi⟩
  rcases hlo with hlo | hlo <;> rcases hhi with hhi | hhi <;> omega

/-- The upper top profile coefficient is nonzero. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.oneFiber_upper_profile_top_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData F Dhi)
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
theorem QsOtherFacetPrUnitLeftContactFrontierData.oneFiber_lower_profile_top_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo)
    {Dhi : QsOtherFacetPrPairReesData C P S F.highest.n}
    (Ahi : QsOtherFacetPrUnitLeftPairFirstInteriorAffineLayerData F Dhi)
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

/-- Upper honest unit interior moment matrix at its top longitudinal degree. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.oneFiber_upper_moment_top_coeff
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo)
    (hdiag : Alo.j = Alo.k) :
    (fun r s =>
      (parallelStaircaseMomentHessian 1 Alo.k Alo.j
        Alo.coefficientProfile r s).coeff Alo.k) =
      Alo.coefficientProfile.coeff Alo.k •
        fieldExponentHessianCore
          ![(Alo.k : K), 0, 1, (1 : K) * (Alo.k : K)] := by
  subst Alo.j
  exact HC4.Polynomial.coeff_upperMode_parallelStaircase
    1 Alo.k Alo.coefficientProfile

/-- Lower honest unit interior moment matrix at its top longitudinal degree. -/
theorem QsOtherFacetPrUnitLeftContactFrontierData.oneFiber_lower_moment_top_coeff
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    (F : QsOtherFacetPrUnitLeftContactFrontierData C P S R)
    {Dlo : QsOtherFacetPrUnitLeftPlanarContactReesData F}
    (Alo : QsOtherFacetPrUnitLeftFirstInteriorAffineLayerData Dlo)
    (hdiag : Alo.j + 2 = Alo.k) :
    (fun r s =>
      (parallelStaircaseMomentHessian 1 Alo.k Alo.j
        Alo.coefficientProfile r s).coeff (Alo.k - 1)) =
      Alo.coefficientProfile.coeff (Alo.k - 1) •
        fieldExponentHessianCore
          ![((Alo.k - 1 : ℕ) : K), 1, 0,
            (1 : K) * ((Alo.k - 1 : ℕ) : K)] := by
  have hk : 2 ≤ Alo.k := by omega
  have hj : Alo.j = Alo.k - 2 := by omega
  rw [hj]
  exact HC4.Polynomial.coeff_lowerMode_parallelStaircase
    1 Alo.k hk Alo.coefficientProfile

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
