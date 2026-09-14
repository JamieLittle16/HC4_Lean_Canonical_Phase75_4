import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryProfileHessianEulerReduction
import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryCarrierEuler
import Mathlib.Tactic

/-!
# A19 stationary parameter/depth directions in source coordinates

The two stationary indices have especially simple source-honest coordinate
representatives on the planar carrier.  Writing `Q` for the stationary
ramified family, `r` for `stationaryWeight`, and
`M = n-E_0-E_1` for stationary depth, the three first-order Euler equations
imply

    V E_tau Q = r (E_3 - V E_2) Q,

and

    ell V M Q = (n-1) (E_3 - V E_1) Q.

These are denominator-free integer coordinate changes.  The first follows by
combining stationary weighted Euler with the monomial-curve equation; the
second is `-V * wall + (n-1) * curve`.  They are the exact source-coordinate
bridge needed by the final cleared-Schur/profile determinant comparison.
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

/-- **Stationary parameter direction in the active `(2,3)` source plane.** -/
theorem stationaryRamifiedFamily_parameterActiveEuler
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
        familyParameterEuler D.stationaryRamifiedFamily =
      MvPolynomial.C (Polynomial.C (F.stationaryWeight : K)) *
        (HC4.Polynomial.mvEuler (3 : Fin 4) D.stationaryRamifiedFamily -
          MvPolynomial.C (Polynomial.C (F.V : K)) *
            HC4.Polynomial.mvEuler (2 : Fin 4)
              D.stationaryRamifiedFamily) := by
  have hw := D.stationaryRamifiedFamily_weightedEuler hthree houtThree
  have hc := D.stationaryRamifiedFamily_curveEuler hthree houtThree
  linear_combination
    MvPolynomial.C (Polynomial.C (F.V : K)) * hw +
      MvPolynomial.C (Polynomial.C (F.stationaryWeight : K)) * hc

/-- **Stationary depth direction modulo the active source plane.** -/
theorem stationaryRamifiedFamily_depthActiveEuler
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
        (Polynomial.C ((F.locked.ell : K) * (F.V : K))) *
        D.stationaryDepthEuler D.stationaryRamifiedFamily =
      MvPolynomial.C (Polynomial.C ((F.highest.n : K) - 1)) *
        (HC4.Polynomial.mvEuler (3 : Fin 4) D.stationaryRamifiedFamily -
          MvPolynomial.C (Polynomial.C (F.V : K)) *
            HC4.Polynomial.mvEuler (1 : Fin 4)
              D.stationaryRamifiedFamily) := by
  have hw := D.stationaryRamifiedFamily_wallEuler hthree houtThree
  have hc := D.stationaryRamifiedFamily_curveEuler hthree houtThree
  have hn1 :
      (MvPolynomial.C (Polynomial.C ((F.highest.n : K) - 1)) :
        MvPolynomial (Fin 4) (Polynomial K)) =
        MvPolynomial.C (Polynomial.C (F.highest.n : K)) - 1 := by
    simp only [map_sub, map_one]
  unfold stationaryDepthEuler
  rw [hn1]
  simp only [map_add, map_sub, map_mul, map_one] at hw hc ⊢
  linear_combination
    -(MvPolynomial.C (Polynomial.C (F.V : K))) * hw +
      (MvPolynomial.C (Polynomial.C (F.highest.n : K)) - 1) * hc

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation