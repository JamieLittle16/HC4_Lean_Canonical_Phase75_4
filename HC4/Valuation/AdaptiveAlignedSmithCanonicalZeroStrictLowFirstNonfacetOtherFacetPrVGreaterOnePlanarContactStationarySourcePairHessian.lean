import HC4.Valuation.AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetOtherFacetPrVGreaterOnePlanarContactStationaryProfileHessianEulerReduction
import Mathlib.Tactic

/-!
# A19 stationary source-pair Hessian bridge

The final stationary Schur/profile comparison must retain the falling-Euler
correction.  The stationary parameter is not literally the complementary
source-pair Euler direction: on the ramified family

    E_tau Q + r Q = r (E_0 + E_1) Q.

Consequently the falling parameter Hessian differs from the naive square of
the source-pair direction by an explicit first-Euler correction.  This module
isolates that correction before any Schur calculation.

Write `S = E_0 + E_1` and `S(S-1)` for its falling second Euler operator.  Then
on the actual stationary ramified family

    E_tau(S Q) = r S(S-1) Q,

and hence

    H_tau,tau + (r+1) E_tau Q = r^2 S(S-1) Q.

These are whole-family identities in the source ring.  No division,
localization, support reconstruction, or new hypothesis is introduced.
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

/-- The complementary source-pair Euler operator `S = E_0 + E_1`. -/
noncomputable def stationarySourcePairEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (_D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  HC4.Polynomial.mvEuler (0 : Fin 4) Q +
    HC4.Polynomial.mvEuler (1 : Fin 4) Q

/-- Falling second source-pair Euler operator `S(S-1)`. -/
noncomputable def stationarySourcePairFallingEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    MvPolynomial (Fin 4) (Polynomial K) :=
  D.stationarySourcePairEuler (D.stationarySourcePairEuler Q) -
    D.stationarySourcePairEuler Q

/-- The source-pair Euler operator is additive. -/
theorem stationarySourcePairEuler_add
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (A B : MvPolynomial (Fin 4) (Polynomial K)) :
    D.stationarySourcePairEuler (A + B) =
      D.stationarySourcePairEuler A + D.stationarySourcePairEuler B := by
  apply MvPolynomial.ext
  intro e
  simp only [stationarySourcePairEuler, MvPolynomial.coeff_add, coeff_mvEuler]
  ring

/-- Ground-field scalars commute with the source-pair Euler operator. -/
theorem stationarySourcePairEuler_groundScalar_mul
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (a : K)
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    D.stationarySourcePairEuler
        (MvPolynomial.C (Polynomial.C a) * Q) =
      MvPolynomial.C (Polynomial.C a) * D.stationarySourcePairEuler Q := by
  apply MvPolynomial.ext
  intro e
  simp only [stationarySourcePairEuler, MvPolynomial.coeff_add,
    MvPolynomial.coeff_C_mul, coeff_mvEuler]
  ring

/-- Source-pair Euler commutes with family-parameter Euler differentiation. -/
theorem stationarySourcePairEuler_familyParameterEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    D.stationarySourcePairEuler (familyParameterEuler Q) =
      familyParameterEuler (D.stationarySourcePairEuler Q) := by
  apply MvPolynomial.ext
  intro e
  simp only [stationarySourcePairEuler, MvPolynomial.coeff_add,
    coeff_mvEuler, coeff_familyParameterEuler,
    Polynomial.derivative_add, Polynomial.derivative_mul,
    Polynomial.derivative_natCast, zero_mul, zero_add]
  ring

/-- Iterating `S` is its falling second iterate plus its first iterate. -/
theorem stationarySourcePairEuler_iterate
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (Q : MvPolynomial (Fin 4) (Polynomial K)) :
    D.stationarySourcePairEuler (D.stationarySourcePairEuler Q) =
      D.stationarySourcePairFallingEuler Q +
        D.stationarySourcePairEuler Q := by
  unfold stationarySourcePairFallingEuler
  ring

/-- Weighted Euler in source-pair notation. -/
theorem stationaryRamifiedFamily_weightedEuler_pair
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    familyParameterEuler D.stationaryRamifiedFamily +
        MvPolynomial.C (Polynomial.C (F.stationaryWeight : K)) *
          D.stationaryRamifiedFamily =
      MvPolynomial.C (Polynomial.C (F.stationaryWeight : K)) *
        D.stationarySourcePairEuler D.stationaryRamifiedFamily := by
  simpa [stationarySourcePairEuler, mul_add] using
    D.stationaryRamifiedFamily_weightedEuler hthree houtThree

/-- **Parameter derivative of the source-pair direction.**
On the stationary ramified family, `E_tau(SQ) = r S(S-1)Q`. -/
theorem stationaryRamifiedFamily_parameterSourcePairEuler
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    familyParameterEuler
        (D.stationarySourcePairEuler D.stationaryRamifiedFamily) =
      MvPolynomial.C (Polynomial.C (F.stationaryWeight : K)) *
        D.stationarySourcePairFallingEuler D.stationaryRamifiedFamily := by
  have h := congrArg
    (fun Q : MvPolynomial (Fin 4) (Polynomial K) =>
      D.stationarySourcePairEuler Q)
    (D.stationaryRamifiedFamily_weightedEuler_pair hthree houtThree)
  rw [D.stationarySourcePairEuler_add,
    D.stationarySourcePairEuler_familyParameterEuler,
    D.stationarySourcePairEuler_groundScalar_mul,
    D.stationarySourcePairEuler_groundScalar_mul,
    D.stationarySourcePairEuler_iterate] at h
  linear_combination h

/-- **Corrected source-pair formula for the stationary parameter Hessian.**
The extra `(r+1) E_tau Q` term is exactly the falling-Euler correction that
prevents the raw complementary Hessian from being identified naively with the
profile Hessian. -/
theorem stationaryProfileHessian00Family_sourcePair
    {C : AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData
      T .qs}
    {P : QsOtherFacetPlanarCarrierPackage C .pr}
    {S : QsOtherFacetPlanarHighestPairSlicePackage C .pr P}
    {R : QsOtherFacetContactQuadraticReesPackage C}
    {F : QsOtherFacetPrLeftVContactFrontierData C P S R}
    (D : QsOtherFacetPrLeftVPlanarContactReesData F)
    (hthree : MvRankThreeOnFacet .qs C.ray.facetExponent)
    (houtThree : MvRankThreeOnFacet .pr C.ray.outsideExponent) :
    D.stationaryProfileHessian00Family +
        MvPolynomial.C
          (Polynomial.C ((F.stationaryWeight : K) + 1)) *
          familyParameterEuler D.stationaryRamifiedFamily =
      MvPolynomial.C
          (Polynomial.C ((F.stationaryWeight : K) ^ 2)) *
        D.stationarySourcePairFallingEuler D.stationaryRamifiedFamily := by
  have hfall :=
    D.stationaryRamifiedFamily_fallingParameterRow hthree houtThree
  have hpair :=
    D.stationaryRamifiedFamily_parameterSourcePairEuler hthree houtThree
  have hsplit :
      familyParameterEuler
          (D.stationarySourcePairEuler D.stationaryRamifiedFamily) =
        familyParameterEuler
            (HC4.Polynomial.mvEuler (0 : Fin 4)
              D.stationaryRamifiedFamily) +
          familyParameterEuler
            (HC4.Polynomial.mvEuler (1 : Fin 4)
              D.stationaryRamifiedFamily) := by
    rw [stationarySourcePairEuler, familyParameterEuler_add]
  unfold stationaryProfileHessian00Family
  rw [← hsplit] at hfall
  rw [hpair] at hfall
  simpa only [map_pow] using hfall

end QsOtherFacetPrLeftVPlanarContactReesData

end AdaptiveAlignedSmithCanonicalZeroStrictLowFirstNonfacetCrossFacetData

end

end HC4.Valuation
