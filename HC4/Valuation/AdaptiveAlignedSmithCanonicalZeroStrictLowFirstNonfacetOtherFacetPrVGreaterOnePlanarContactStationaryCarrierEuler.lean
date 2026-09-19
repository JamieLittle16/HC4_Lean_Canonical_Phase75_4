import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryWeightedEuler
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarCarrierEuler
import Mathlib.Tactic

/-!
# A19 planar Euler equations on the stationary ramified contact family

The denominator-clearing stationary ramification changes only the parameter
coefficient attached to each literal source monomial.  It does not change that
monomial's four source exponents.  Consequently the two affine Euler equations
of the planar carrier lift verbatim to the actual ramified singular contact
family.

Together with `stationaryRamifiedFamily_weightedEuler`, these equations give
three exact whole-family linear relations among the four source Euler rows and
the parameter Euler row.  This is the source-honest input for the final
stationary Schur/profile Hessian identification.
-/

namespace HC4.Valuation

noncomputable section

open HC4.Newton HC4.Polynomial HC4.Toric
open Polynomial

universe u
variable {K : Type u} [Field K] [CharZero K] [IsAlgClosed K]

namespace AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

variable {state : ScaleAwareAdaptiveGeometricRestartState (K := K)}
variable {T : AdaptiveAlignedSmithCanonicalZeroStrictLowSingularTerminalData
  (K := K) state}

namespace QsOtherFacetPrLeftVPlanarContactReesData

/-- The first affine planar Euler equation survives the stationary
ramification coefficientwise. -/
theorem stationaryRamifiedFamily_wallEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    MvPolynomial.C
        (Polynomial.C
          (((F.highest.n : K) - 1) + (F.locked.ell : K))) *
          HC4.Polynomial.mvEuler (0 : Fin 4) D.stationaryRamifiedFamily +
      MvPolynomial.C (Polynomial.C (F.locked.ell : K)) *
          HC4.Polynomial.mvEuler (1 : Fin 4) D.stationaryRamifiedFamily +
      MvPolynomial.C
          (Polynomial.C ((F.highest.n : K) - 1)) *
          HC4.Polynomial.mvEuler (2 : Fin 4) D.stationaryRamifiedFamily =
    MvPolynomial.C
        (Polynomial.C
          (((F.highest.n : K) - 1) +
            (F.locked.ell : K) * (F.highest.n : K))) *
      D.stationaryRamifiedFamily := by
  classical
  apply MvPolynomial.ext
  intro e
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, coeff_mvEuler]
  by_cases he : e ∈ P.carrier.support
  · let q := F.stationaryTotalDegree -
      F.stationaryWeight * (F.highest.n - (e 0 + e 1))
    have hcoeff := D.coeff_stationaryRamifiedFamily_of_carrier_mem
      hthree houtThree he
    have hcoeffq :
        MvPolynomial.coeff e D.stationaryRamifiedFamily =
          Polynomial.X ^ q * Polynomial.C (MvPolynomial.coeff e P.carrier) := by
      simpa [q] using hcoeff
    rw [hcoeffq]
    have hs := F.support_wallEuler_scalar hthree houtThree he
    have hP := congrArg Polynomial.C hs
    simp only [map_add, map_sub, map_mul, map_one, map_natCast] at hP ⊢
    linear_combination
      (Polynomial.X ^ q * Polynomial.C (MvPolynomial.coeff e P.carrier)) * hP
  · have hcoeff0 :
        MvPolynomial.coeff e D.stationaryRamifiedFamily = 0 := by
      unfold stationaryRamifiedFamily parameterRamificationFamily
      rw [MvPolynomial.coeff_map]
      unfold QsOtherFacetPrLeftVPlanarContactReesData.family
      rw [reverseWeightedReesFamily_coeff]
      rw [if_neg he]
      simp
    rw [hcoeff0]
    simp

/-- The monomial-curve affine Euler equation also survives the stationary
ramification coefficientwise. -/
theorem stationaryRamifiedFamily_curveEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    MvPolynomial.C (Polynomial.C (F.V : K)) *
          HC4.Polynomial.mvEuler (0 : Fin 4) D.stationaryRamifiedFamily +
        MvPolynomial.C (Polynomial.C (F.V : K)) *
          HC4.Polynomial.mvEuler (1 : Fin 4) D.stationaryRamifiedFamily +
        MvPolynomial.C (Polynomial.C (F.V : K)) *
          HC4.Polynomial.mvEuler (2 : Fin 4) D.stationaryRamifiedFamily =
      MvPolynomial.C (Polynomial.C (F.V : K)) *
          D.stationaryRamifiedFamily +
        HC4.Polynomial.mvEuler (3 : Fin 4) D.stationaryRamifiedFamily := by
  classical
  apply MvPolynomial.ext
  intro e
  simp only [MvPolynomial.coeff_add, MvPolynomial.coeff_C_mul, coeff_mvEuler]
  by_cases he : e ∈ P.carrier.support
  · let q := F.stationaryTotalDegree -
      F.stationaryWeight * (F.highest.n - (e 0 + e 1))
    have hcoeff := D.coeff_stationaryRamifiedFamily_of_carrier_mem
      hthree houtThree he
    have hcoeffq :
        MvPolynomial.coeff e D.stationaryRamifiedFamily =
          Polynomial.X ^ q * Polynomial.C (MvPolynomial.coeff e P.carrier) := by
      simpa [q] using hcoeff
    rw [hcoeffq]
    have hs := F.support_curveEuler_scalar hthree houtThree he
    have hP := congrArg Polynomial.C hs
    simp only [map_add, map_sub, map_mul, map_one, map_natCast] at hP ⊢
    linear_combination
      (Polynomial.X ^ q * Polynomial.C (MvPolynomial.coeff e P.carrier)) * hP
  · have hcoeff0 :
        MvPolynomial.coeff e D.stationaryRamifiedFamily = 0 := by
      unfold stationaryRamifiedFamily parameterRamificationFamily
      rw [MvPolynomial.coeff_map]
      unfold QsOtherFacetPrLeftVPlanarContactReesData.family
      rw [reverseWeightedReesFamily_coeff]
      rw [if_neg he]
      simp
    rw [hcoeff0]
    simp

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
