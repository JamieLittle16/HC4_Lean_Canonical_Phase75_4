import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryRamification
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactFamilyActiveConstant
import HC4.Valuation.PrimitiveSmithEndpoint
import Mathlib.Tactic

/-!
# A19 stationary ramified active pivot

The denominator-clearing stationary ramification is a positive coefficient-ring
base change.  Hence it preserves the parameter-zero special fibre of the
actual singular planar-contact family.  In particular the source-honest
nonzero `(2,3)` Hessian principal minor survives unchanged as the constant
coefficient of the active Schur determinant.

This is the exact division-free pivot needed by the stationary Schur/profile
adapter.  No localization, auxiliary clock identification, or new geometric
assumption is introduced.
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

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- Positive stationary ramification preserves the honest parameter-zero
special fibre coefficientwise. -/
theorem polynomialFamilySpecialFiber_stationaryRamifiedFamily
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F) :
    polynomialFamilySpecialFiber D.stationaryRamifiedFamily =
      polynomialFamilySpecialFiber D.family := by
  classical
  apply MvPolynomial.ext
  intro e
  rw [coeff_polynomialFamilySpecialFiber, coeff_polynomialFamilySpecialFiber]
  unfold stationaryRamifiedFamily parameterRamificationFamily
  rw [MvPolynomial.coeff_map]
  have hpos : 0 < F.highest.n - 1 := by
    have hn := F.highest.n_two_le
    omega
  exact constantCoeff_parameterRamificationHom
    (K := K) (F.highest.n - 1) hpos (MvPolynomial.coeff e D.family)

/-- The ramified family's `(2,3)` active Schur determinant has the same
nonzero constant parameter coefficient as the original planar-contact family. -/
theorem stationaryRamifiedFamily_activeDet_coeff_zero_ne_zero
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    (permutedFamilyHessianFourBlock
      qsPrSuperfaceSchurPermutation D.stationaryRamifiedFamily).activeDet.coeff 0 ≠ 0 := by
  rw [permutedFamilyHessianFourBlock_activeDet_coeff_zero_eq_specialFiber_minor]
  rw [D.polynomialFamilySpecialFiber_stationaryRamifiedFamily]
  simpa [qsPrSuperfaceSchurPermutation] using
    D.specialFiber_hessianPrincipalMinor_two_three_ne_zero hthree houtThree

/-- Whole-polynomial cancellation by the stationary ramified active pivot. -/
theorem cancel_stationaryRamifiedFamily_activeDet
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent)
    (B : Polynomial (MvPolynomial (Fin 4) K))
    (hprod : ∀ n : ℕ,
      (((permutedFamilyHessianFourBlock
          qsPrSuperfaceSchurPermutation D.stationaryRamifiedFamily).activeDet * B).coeff n) = 0) :
    B = 0 := by
  let A := (permutedFamilyHessianFourBlock
    qsPrSuperfaceSchurPermutation D.stationaryRamifiedFamily).activeDet
  have hA0 : A.coeff 0 ≠ 0 := by
    simpa [A] using
      D.stationaryRamifiedFamily_activeDet_coeff_zero_ne_zero hthree houtThree
  have hAB : A * B = 0 := by
    apply Polynomial.ext
    intro n
    simpa [A] using hprod n
  have hA : A ≠ 0 := by
    intro hzero
    apply hA0
    rw [hzero]
    simp
  exact (mul_eq_zero.mp hAB).resolve_left hA

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
